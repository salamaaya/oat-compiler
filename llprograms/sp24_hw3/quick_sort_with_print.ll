declare void @ll_puts(i8*)
declare i8* @ll_ltoa(i64)

@original_list = global [5 x i64] [ i64 2, i64 1, i64 3, i64 5, i64 4 ]
@sorted_list = global [5 x i64] [ i64 1, i64 2, i64 3, i64 4, i64 5 ]

@pre_swap_list = global [5 x i64] [ i64 2, i64 1, i64 3, i64 5, i64 4 ]
@swapped_list = global [5 x i64] [ i64 3, i64 1, i64 2, i64 5, i64 4 ]

@pre_partition_list = global [5 x i64] [ i64 2, i64 1, i64 3, i64 5, i64 4 ]
@partitioned_list = global [5 x i64] [ i64 2, i64 1, i64 3, i64 4, i64 5 ]

define void @swap([5 x i64]* %list, i64 %i, i64 %j) {
    %iptr = getelementptr [5 x i64], [5 x i64]* %list, i64 0, i64 %i
    %jptr = getelementptr [5 x i64], [5 x i64]* %list, i64 0, i64 %j
    %ival = load i64, i64* %iptr
    %jval = load i64, i64* %jptr
    store i64 %ival, i64* %jptr
    store i64 %jval, i64* %iptr
    ret void
}

define i64 @partition([5 x i64]* %list, i64 %lo, i64 %hi) {
    ; hi = last index of array
    %pivotptr = getelementptr [5 x i64], [5 x i64]* %list, i64 0, i64 %hi
    %pivotval = load i64, i64* %pivotptr
    
    %tmp = sub i64 %lo, 1
    %i = alloca i64
    store i64 %tmp, i64* %i
    %j = alloca i64
    store i64 %lo, i64* %j
    br label %loop
loop:
    %itmp = load i64, i64* %i
    %jtmp = load i64, i64* %j
    %cmp1 = icmp sle i64 %jtmp, %hi
    br i1 %cmp1, label %cont, label %end
cont:
    %jptr = getelementptr [5 x i64], [5 x i64]* %list, i64 0, i64 %jtmp
    %jval = load i64, i64* %jptr
    %cmp2 = icmp slt i64 %jval, %pivotval
    br i1 %cmp2, label %swap, label %increment
swap:
    %b = add i64 1, %itmp
    store i64 %b, i64* %i
    %itmp2 = load i64, i64* %i
    call void @swap([5 x i64]* %list, i64 %itmp2, i64 %jtmp)
    br label %increment
increment:
    %a = add i64 1, %jtmp
    store i64 %a, i64* %j
    br label %loop
end:
    %itmp3 = load i64, i64* %i
    %c = add i64 1, %itmp3
    call void @swap([5 x i64]* %list, i64 %c, i64 %hi)
    ret i64 %c
}

define void @quicksort ([5 x i64]* %list, i64 %lo, i64 %hi) {
    ; hi = last index of array
    %cmp1 = icmp slt i64 %lo, %hi
    br i1 %cmp1, label %sort, label %endsort
sort:
    %pivotind = call i64 @partition([5 x i64]* %list, i64 %lo, i64 %hi)
    %pivotindmin1 = sub i64 %pivotind, 1
    call void @quicksort([5 x i64]* %list, i64 %lo, i64 %pivotindmin1)
    %pivotindadd1 = add i64 %pivotind, 1
    call void @quicksort([5 x i64]* %list, i64 %pivotindadd1, i64 %hi)
    br label %endsort
endsort:
    ret void
}

define i64 @check ([5 x i64]* %r, [5 x i64]* %s) {
    ; returns 0 if equal, 1 if not equal
    %i = alloca i64
    store i64 0, i64* %i
    br label %loop
loop:
    %count = load i64, i64* %i
    %cmp1 = icmp eq i64 %count, 5
    br i1 %cmp1, label %equal, label %check
check:
    %rptr = getelementptr [5 x i64], [5 x i64]* %r, i32 0, i64 %count
    %sptr = getelementptr [5 x i64], [5 x i64]* %s, i32 0, i64 %count
    %rval = load i64, i64* %rptr
    %sval = load i64, i64* %sptr
    %cmp2 = icmp eq i64 %rval, %sval
    %a = add i64 1, %count
    store i64 %a, i64* %i
    br i1 %cmp2, label %loop, label %noteq
equal:
    ret i64 0
noteq:
    ret i64 1
}

define void @printarr([5 x i64]* %list, i64 %lo, i64 %hi) {
    ; hi = length of array
    %i = alloca i64
    store i64 %lo, i64* %i
    br label %loop
loop:
    %count = load i64, i64* %i
    %cmp1 = icmp eq i64 %count, %hi
    br i1 %cmp1, label %end, label %check
check:
    %ptr = getelementptr [5 x i64], [5 x i64]* %list, i32 0, i64 %count
    %val = load i64, i64* %ptr
    %bug = call i8* @ll_ltoa(i64 %val)
    call void @ll_puts(i8* %bug)
    %a = add i64 1, %count
    store i64 %a, i64* %i
    br label %loop
end:
    ret void
}

define i64 @main(i64 %argc, i8** %arcv) {
  ; sort test
  call void @printarr([5 x i64]* @original_list, i64 0, i64 5)
  call void @quicksort([5 x i64]* @original_list, i64 0, i64 4)
  call void @printarr([5 x i64]* @original_list, i64 0, i64 5)
  %1 = call i64 @check([5 x i64]* @original_list, [5 x i64]* @sorted_list)

  ; swap test
  call void @printarr([5 x i64]* @pre_swap_list, i64 0, i64 5)
  call void @swap([5 x i64]* @pre_swap_list, i64 0, i64 2)
  call void @printarr([5 x i64]* @pre_swap_list, i64 0, i64 5)
  %2 = call i64 @check([5 x i64]* @pre_swap_list, [5 x i64]* @swapped_list)

  ; partition test
  call void @printarr([5 x i64]* @pre_partition_list, i64 0, i64 5)
  %pi = call i64 @partition([5 x i64]* @pre_partition_list, i64 0, i64 4)
  %pis = call i8* @ll_ltoa(i64 %pi)
  call void @ll_puts(i8* %pis)
  call void @printarr([5 x i64]* @pre_partition_list, i64 0, i64 5)
  %3 = call i64 @check([5 x i64]* @pre_partition_list, [5 x i64]* @partitioned_list)
  
  %4 = add i64 %1, %2
  %5 = add i64 %3, %4
  
  ret i64 %5
}