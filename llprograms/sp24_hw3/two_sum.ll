; judtin, jasyan
; two sum: given a list nums and int target, return the sum of the two indices whose values add up to target

%array = type [10 x i64]

%pair = type [2 x i64]

@target = global i64 800
@array_size = global i64 10
@nums = global %array [ i64 123, i64 934, i64 3, i64 342, i64 732, i64 396, i64 502, i64 221, i64 6, i64 797 ]

define i64 @two_sum(i64* %arr) {
    %i_ptr = alloca i64
    store i64 0, i64* %i_ptr

    %j_ptr = alloca i64
    %array_size_val = load i64, i64* @array_size

    %result = alloca i64
    store i64 -1, i64* %result

    br label %outer_loop

outer_loop:
    store i64 0, i64* %j_ptr
    br label %inner_loop

inner_loop:
    %i = load i64, i64* %i_ptr
    %j = load i64, i64* %j_ptr

    %i_elem_ptr = getelementptr %array, %array* %arr, i32 0, i64 %i
    %j_elem_ptr = getelementptr %array, %array* %arr, i32 0, i64 %j
    %i_elem = load i64, i64* %i_elem_ptr
    %j_elem = load i64, i64* %j_elem_ptr

    %sum = add i64 %i_elem, %j_elem

    %target_val = load i64, i64* @target
    %cmp = icmp eq i64 %target_val, %sum
    
    br i1 %cmp, label %found, label %not_found

found:
    %ans = add i64 %i, %j
    store i64 %ans, i64* %result
    br label %end_loop

not_found:
    %j_plus_1 = add i64 %j, 1
    store i64 %j_plus_1, i64* %j_ptr
 
    %cmp1 = icmp eq i64 %array_size_val, %j
    br i1 %cmp1, label %end_inner_loop, label %inner_loop

end_inner_loop:
    %i_plus_1 = add i64 %i, 1
    store i64 %i_plus_1, i64* %i_ptr

    %cmp2 = icmp eq i64 %array_size_val, %i
    br i1 %cmp2, label %end_loop, label %outer_loop

end_loop:
    %res_val = load i64, i64* %result
    ret i64 %res_val
}

define i64 @main(i64 %argc, i8** %arcv) {
  %ans = call i64 @two_sum(%array* @nums)
  ret i64 %ans
}


