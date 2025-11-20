%struct = type { i64, [10 x i64] }

@gbl = global %struct { i64 10, [10 x i64] [ i64 5, i64 1, i64 3, i64 7, i64 4, i64 8, i64 2, i64 6, i64 9, i64 10] }

@expected_arr = global %struct { i64 10, [10 x i64] [ i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8, i64 9, i64 10] }


define i64 @is_sorted(%struct* %arr1, %struct* %arr2) {
  %size_ptr = getelementptr %struct, %struct* %arr1, i32 0, i32 0
  %iter_ptr = alloca i64
  store i64 0, i64* %iter_ptr
  br label %loop_entry
loop_entry:
  %iter = load i64, i64* %iter_ptr
  %size = load i64, i64* %size_ptr
  %cmp = icmp slt i64 %iter, %size
  br i1 %cmp, label %loop_body, label %exit
loop_body:
  %iter1 = load i64, i64* %iter_ptr
  %val1_ptr = getelementptr %struct, %struct* %arr1, i32 0, i32 1, i64 %iter1
  %val2_ptr = getelementptr %struct, %struct* %arr2, i32 0, i32 1, i64 %iter1
  %val1 = load i64, i64* %val1_ptr
  %val2 = load i64, i64* %val2_ptr
  %new_iter = add i64 %iter1, 1
  store i64 %new_iter, i64* %iter_ptr
  %cmp1 = icmp eq i64 %val1, %val2
  br i1 %cmp1, label %loop_entry, label %exit_false
exit_false:
  ret i64 0
exit:
  ret i64 1
}


define i64 @sort(%struct* %arr) {
  %size_ptr = getelementptr %struct, %struct* %arr, i32 0, i32 0
  %i_ptr = alloca i64
  %j_ptr = alloca i64
  %min_idx_ptr = alloca i64
  store i64 0, i64* %i_ptr
  br label %loop_entry1
loop_entry1:
  %i_val = load i64, i64* %i_ptr
  %size_val = load i64, i64* %size_ptr
  %loop_1_ub = sub i64 %size_val, 1
  %cmp = icmp slt i64 %i_val, %loop_1_ub
  br i1 %cmp, label %loop_body1, label %exit 
loop_body1:
  %min_idx_val = load i64, i64* %i_ptr
  store i64 %min_idx_val, i64* %min_idx_ptr
  %i_val1 = load i64, i64* %i_ptr
  %i_val2 = add i64 1, %i_val1
  store i64 %i_val2, i64* %j_ptr
  br label %entry2
entry2:
  %size_val1 = load i64, i64* %size_ptr
  %j_val2 = load i64, i64* %j_ptr
  %cmp1 = icmp slt i64 %j_val2, %size_val1
  br i1 %cmp1, label %loop_body2, label %swap 
loop_body2:
  %min_idx_val1 = load i64, i64* %min_idx_ptr
  %j_val3 = load i64, i64* %j_ptr
  %arr_min_idx_ptr = getelementptr %struct, %struct* %arr, i32 0, i32 1, i64 %min_idx_val1
  %arr_j_ptr = getelementptr %struct, %struct* %arr, i32 0, i32 1, i64 %j_val3
  %arr_min_idx_val = load i64, i64* %arr_min_idx_ptr
  %arr_j_val = load i64, i64* %arr_j_ptr
  %cmp2 = icmp slt i64 %arr_j_val, %arr_min_idx_val
  br i1 %cmp2, label %update_min_idx, label %merge
update_min_idx:
  store i64 %j_val3, i64* %min_idx_ptr
  br label %merge
merge:
  %j_val4 = add i64 1, %j_val3
  store i64 %j_val4, i64* %j_ptr
  br label %entry2
swap:
  %min_idx_val2 = load i64, i64* %min_idx_ptr
  %i_val3 = load i64, i64* %i_ptr
  %arr_min_idx_ptr_1 = getelementptr %struct, %struct* %arr, i32 0, i32 1, i64 %min_idx_val2
  %arr_i_ptr = getelementptr %struct, %struct* %arr, i32 0, i32 1, i64 %i_val3

  %arr_min_idx_val_1 = load i64, i64* %arr_min_idx_ptr_1
  %arr_i_val = load i64, i64* %arr_i_ptr

  store i64 %arr_min_idx_val_1, i64* %arr_i_ptr
  store i64 %arr_i_val, i64* %arr_min_idx_ptr_1

  %i_val4 = add i64 1, %i_val3
  store i64 %i_val4, i64* %i_ptr

  br label %loop_entry1
exit:
  ret i64 0
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @sort(%struct* @gbl)
  %ret_val = call i64 @is_sorted(%struct* @gbl, %struct* @expected_arr)
  ret i64 %ret_val
}

