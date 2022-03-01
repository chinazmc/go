// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Central free lists.
//
// See malloc.go for an overview.
//
// The MCentral doesn't actually contain the list of free objects; the MSpan does.
// Each MCentral is two lists of MSpans: those with free objects (c->nonempty)
// and those that are completely allocated (c->empty).

package runtime

// Central list of free objects of a given size.
type mcentral struct {
	lock      mutex
	sizeclass int32 // 规格
	nonempty  mspan // list of spans with a free object// 链表：尚有空闲 object 的 span
	empty     mspan // list of spans with no free objects (or cached in an mcache)// 链表：没有空闲 object，或已被 cache 取走的 span
}

// Initialize a single central free list.
func mCentral_Init(c *mcentral, sizeclass int32) {
	c.sizeclass = sizeclass
	mSpanList_Init(&c.nonempty)
	mSpanList_Init(&c.empty)
}

// Allocate a span to use in an MCache.
func mCentral_CacheSpan(c *mcentral) *mspan {
	// 清理（ sweep）垃圾 ...
	// Deduct credit for this span allocation and sweep if necessary.
	deductSweepCredit(uintptr(class_to_size[c.sizeclass]), 0)

	lock(&c.lock)
	sg := mheap_.sweepgen
retry:
	var s *mspan
	// 遍历 nonempty 链表
	for s = c.nonempty.next; s != &c.nonempty; s = s.next {
		// 需要清理的 span
		if s.sweepgen == sg-2 && cas(&s.sweepgen, sg-2, sg-1) {
			// 因为要交给 cache 使用，所以转移到 empty 链表
			mSpanList_Remove(s)
			mSpanList_InsertBack(&c.empty, s)
			unlock(&c.lock)
			// 垃圾清理
			mSpan_Sweep(s, true)
			goto havespan
		}
		// 忽略正在清理的 span
		if s.sweepgen == sg-1 {
			// the span is being swept by background sweeper, skip
			continue
		}
		// we have a nonempty span that does not require sweeping, allocate from it
		// 已清理过的 span
		mSpanList_Remove(s)
		mSpanList_InsertBack(&c.empty, s)
		unlock(&c.lock)
		goto havespan
	}
	// 遍历 empty 链表
	for s = c.empty.next; s != &c.empty; s = s.next {
		// 需要清理的 span
		if s.sweepgen == sg-2 && cas(&s.sweepgen, sg-2, sg-1) {
			// we have an empty span that requires sweeping,
			// sweep it and see if we can free some space in it
			mSpanList_Remove(s)
			// swept spans are at the end of the list
			mSpanList_InsertBack(&c.empty, s)
			unlock(&c.lock)
			mSpan_Sweep(s, true)
			// 清理后有可用的 object
			if s.freelist.ptr() != nil {
				goto havespan
			}
			lock(&c.lock)
			// the span is still empty after sweep
			// it is already in the empty list, so just retry
			// 清理后依然没可用的 object，重试
			goto retry
		}
		// 忽略正在清理的 span
		if s.sweepgen == sg-1 {
			// the span is being swept by background sweeper, skip
			continue
		}
		// already swept empty span,
		// all subsequent ones must also be either swept or in process of sweeping
		// 已清理过，且不为空的 span 都被转移到 noempty 链表
		// 这里剩下的自然都是全空或正在被 cache 使用的，继续循环已没有意义
		break
	}
	unlock(&c.lock)

	// Replenish central list if empty.
	// 如果两个链表里都没 span 可用，扩张
	s = mCentral_Grow(c)
	if s == nil {
		return nil
	}
	lock(&c.lock)
	// 新 span 将被 cache 使用，所以放到 empty 链表尾部
	mSpanList_InsertBack(&c.empty, s)
	unlock(&c.lock)

	// At this point s is a non-empty span, queued at the end of the empty list,
	// c is unlocked.
havespan:
	cap := int32((s.npages << _PageShift) / s.elemsize)
	n := cap - int32(s.ref)
	if n == 0 {
		throw("empty span")
	}
	if s.freelist.ptr() == nil {
		throw("freelist empty")
	}
	// 设置被 cache 使用标志
	s.incache = true
	return s
}

// Return span from an MCache.
func mCentral_UncacheSpan(c *mcentral, s *mspan) {
	lock(&c.lock)

	s.incache = false

	if s.ref == 0 {
		throw("uncaching full span")
	}

	cap := int32((s.npages << _PageShift) / s.elemsize)
	n := cap - int32(s.ref)
	if n > 0 {
		mSpanList_Remove(s)
		mSpanList_Insert(&c.nonempty, s)
	}
	unlock(&c.lock)
}

// Free n objects from a span s back into the central free list c.
// Called during sweep.
// Returns true if the span was returned to heap.  Sets sweepgen to
// the latest generation.
// If preserve=true, don't return the span to heap nor relink in MCentral lists;
// caller takes care of it.
func mCentral_FreeSpan(c *mcentral, s *mspan, n int32, start gclinkptr, end gclinkptr, preserve bool) bool {
	if s.incache {
		throw("freespan into cached span")
	}
	// 判断 span 是否为空（没有空闲 object）
	// Add the objects back to s's free list.
	wasempty := s.freelist.ptr() == nil
	// 将收集到链表合并到 freelist
	end.ptr().next = s.freelist
	s.freelist = start
	s.ref -= uint16(n)
	// 阻止进一步回收
	if preserve {
		// preserve is set only when called from MCentral_CacheSpan above,
		// the span must be in the empty list.
		if s.next == nil {
			throw("can't preserve unlinked span")
		}
		atomicstore(&s.sweepgen, mheap_.sweepgen)
		return false
	}

	lock(&c.lock)
	// 将原本为空的 span 转移到 central.nonempty 链表
	// Move to nonempty if necessary.
	if wasempty {
		mSpanList_Remove(s)
		mSpanList_Insert(&c.nonempty, s)
	}

	// delay updating sweepgen until here.  This is the signal that
	// the span may be used in an MCache, so it must come after the
	// linked list operations above (actually, just after the
	// lock of c above.)
	atomicstore(&s.sweepgen, mheap_.sweepgen)
	// 如果还有 object 被使用，那么终止
	if s.ref != 0 {
		unlock(&c.lock)
		return false
	}
	// 如果收回全部 object，就从 central 交还给 heap
	// s is completely freed, return it to the heap.
	mSpanList_Remove(s)
	s.needzero = 1
	s.freelist = 0
	unlock(&c.lock)
	heapBitsForSpan(s.base()).initSpan(s.layout())
	mHeap_Free(&mheap_, s, 0)
	return true
}

// Fetch a new span from the heap and carve into objects for the free list.
func mCentral_Grow(c *mcentral) *mspan {
	// 查表获取所需页数
	npages := uintptr(class_to_allocnpages[c.sizeclass])
	size := uintptr(class_to_size[c.sizeclass])
	// 计算切分 object 数量
	n := (npages << _PageShift) / size
	// 从 heap 获取 span
	s := mHeap_Alloc(&mheap_, npages, c.sizeclass, false, true)
	if s == nil {
		return nil
	}
	// 切分成 object 链表
	p := uintptr(s.start << _PageShift) //内存地址
	s.limit = p + size*n
	head := gclinkptr(p)
	tail := gclinkptr(p)
	// i==0 iteration already done
	for i := uintptr(1); i < n; i++ {
		p += size
		tail.ptr().next = gclinkptr(p)
		tail = gclinkptr(p)
	}
	if s.freelist.ptr() != nil {
		throw("freelist not empty")
	}
	tail.ptr().next = 0
	s.freelist = head
	//重置在bitmap里的标记
	heapBitsForSpan(s.base()).initSpan(s.layout())
	return s
}
