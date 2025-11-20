%array = type [10 x i64]

@arr = global %array [ i64 10, i64 2, i64 7, i64 4, i64 5, i64 1, i64 9, i64 3, i64 6, i64 8 ]

@sorted_arr = global %array [ i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8, i64 9, i64 10]

define i64 @check_sorted(%array* %expected, %array* %actual) {
  %idx_ptr = alloca i64
  store i64 0, i64* %idx_ptr
  br label %iterate
iterate:
  %idx = load i64, i64* %idx_ptr
  %cmp4 = icmp slt i64 %idx, 10
  br i1 %cmp4, label %check_arrs, label %end_sorted
check_arrs:
  %exp_ptr = getelementptr %array, %array* %expected, i32 0, i64 %idx
  %act_ptr = getelementptr %array, %array* %actual, i32 0, i64 %idx
  %exp_val = load i64, i64* %exp_ptr
  %act_val = load i64, i64* %act_ptr

  %a = add i64 %idx, 1
  store i64 %a, i64* %idx_ptr
  
  %cmp5 = icmp eq i64 %exp_val, %act_val
  br i1 %cmp5, label %iterate, label %end_not_sorted
end_not_sorted:
  ret i64 0
end_sorted:
  ret i64 1
}

define void @insertion_sort(%array* %arr, i64 %len) {
  %i = alloca i64
  store i64 1, i64* %i
  %j = alloca i64
  br label %loop
loop:
  %i_val = load i64, i64* %i
  %cmp1 = icmp eq i64 %i_val, %len
  br i1 %cmp1, label %end, label %loop_body
loop_body:
  %key = getelementptr %array, %array* %arr, i32 0, i64 %i_val
  %key_val = load i64, i64* %key
  %j_val = sub i64 %i_val, 1
  store i64 %j_val, i64* %j
  br label %inner_loop_check
inner_loop_check:
  %j_val = load i64, i64* %j
  %cmp2 = icmp sge i64 %j_val, 0
  br i1 %cmp2, label %inner_loop_check2, label %increment
inner_loop_check2:
  %arr_j = getelementptr %array, %array* %arr, i32 0, i64 %j_val
  %arr_j_val = load i64, i64* %arr_j
  %cmp3 = icmp slt i64 %key_val, %arr_j_val
  br i1 %cmp3, label %inner_loop, label %increment
inner_loop:
  %next_j = add i64 %j_val, 1
  %next_arr_j = getelementptr %array, %array* %arr, i32 0, i64 %next_j
  store i64 %arr_j_val, i64* %next_arr_j
  
  %temp_j = sub i64 %j_val, 1
  store i64 %temp_j, i64* %j
  br label %inner_loop_check
increment:
  %next_j = add i64 %j_val, 1
  %next_arr_j = getelementptr %array, %array* %arr, i32 0, i64 %next_j
  store i64 %key_val, i64* %next_arr_j

  %temp_i = add i64 1, %i_val
  store i64 %temp_i, i64* %i
  br label %loop
end:
  ret void
}

define i64 @main(i64 %argc, i8** %arcv) {
  call void @insertion_sort(%array* @arr, i64 10)
  %1 = call i64 @check_sorted(%array* @sorted_arr, %array* @arr)
  ret i64 %1
}