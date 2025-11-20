%arraystruct = type {[12 x i64]}

; eloic + tom
@unsorted_array_1 = global %arraystruct {[12 x i64] [i64 -95, i64 18, i64 -50, i64 -22, i64 -51, i64 -1, i64 94, i64 6, i64 82, i64 82, i64 -23, i64 44]}
@unsorted_array_2 = global %arraystruct {[12 x i64] [i64 2, i64 79, i64 -8, i64 -86, i64 6, i64 -29, i64 88, i64 -80, i64 2, i64 21, i64 -26, i64 -13]}
@unsorted_array_3 = global %arraystruct {[12 x i64] [i64 16, i64 -1, i64 3, i64 51, i64 30, i64 49, i64 -48, i64 -99, i64 -13, i64 57, i64 -63, i64 29]}
@unsorted_array_4 = global %arraystruct {[12 x i64] [i64 91, i64 87, i64 -80, i64 60, i64 -43, i64 -79, i64 -12, i64 -52, i64 -42, i64 69, i64 87, i64 -86]}
@unsorted_array_5 = global %arraystruct {[12 x i64] [i64 89, i64 89, i64 74, i64 89, i64 -50, i64 7, i64 -46, i64 -37, i64 30, i64 -50, i64 34, i64 -80]}

define i1 @is_sorted(%arraystruct* %arr) {
  %array_end_ptr = alloca i64
  store i64 11, i64* %array_end_ptr
  %array_end = load i64, i64* %array_end_ptr
  %i = alloca i64
  store i64 0, i64* %i
  br label %loop_cond

loop_cond:
  %i_val = load i64, i64* %i
  %loop_cmp = icmp slt i64 %i_val, %array_end 
  br i1 %loop_cmp, label %loop_body, label %sorted

loop_body:
  %curr_ptr = getelementptr %arraystruct, %arraystruct* %arr, i64 0, i32 0, i64 %i_val
  %next_ptr = getelementptr i64, i64* %curr_ptr, i64 1

  %curr_elem = load i64, i64* %curr_ptr
  %next_elem = load i64, i64* %next_ptr

  %elem_cmp = icmp sle i64 %curr_elem, %next_elem
  br i1 %elem_cmp, label %increment, label %not_sorted

increment:
  %next_i = add i64 %i_val, 1
  store i64 %next_i, i64* %i
  br label %loop_cond

not_sorted:
  ret i1 0

sorted:
  ret i1 1
}

define void @swap(i64* %x, i64* %y) {
  %temp1 = load i64, i64* %x
  %temp2 = load i64, i64* %y
  store i64 %temp1, i64* %y
  store i64 %temp2, i64* %x
  ret void
}

define void @bubblesort(%arraystruct* %arr) {
  %length = alloca i64
  store i64 12, i64* %length
  %i = alloca i64
  %j = alloca i64
  br label %outer_loop_entry

outer_loop_entry:
  store i64 0, i64* %i
  %length_val = load i64, i64* %length
  br label %outer_loop_cond

outer_loop_cond:
  %i_val = load i64, i64* %i
  %cmp1 = icmp slt i64 %i_val, %length_val
  br i1 %cmp1, label %inner_loop_entry, label %exit

inner_loop_entry:
  store i64 0, i64* %j
  %i_val_for_j = load i64, i64* %i
  %length_for_j = sub i64 %length_val, 1
  %length_for_j = sub i64 %length_for_j, %i_val_for_j
  br label %inner_loop_cond

inner_loop_cond:
  %j_val = load i64, i64* %j
  %cmp2 = icmp slt i64 %j_val, %length_for_j
  br i1 %cmp2, label %swap_check, label %inner_loop_exit

swap_check:
  %j_plus_1 = add i64 %j_val, 1
  %elem1_ptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %j_val
  %elem2_ptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %j_plus_1
  %elem1 = load i64, i64* %elem1_ptr
  %elem2 = load i64, i64* %elem2_ptr
  %cmp3 = icmp sgt i64 %elem1, %elem2
  br i1 %cmp3, label %do_swap, label %no_swap

do_swap:
  call void @swap(i64* %elem1_ptr, i64* %elem2_ptr)
  br label %no_swap

no_swap:
  %j_inc = add i64 %j_val, 1
  store i64 %j_inc, i64* %j
  br label %inner_loop_cond

inner_loop_exit:
  %i_inc = add i64 %i_val, 1
  store i64 %i_inc, i64* %i
  br label %outer_loop_cond

exit:
  ret void
}


define i1 @main(i64 %argc, i8** %arcv) {
  call void @bubblesort(%arraystruct* @unsorted_array_1, i64 0, i64 11)
  call void @bubblesort(%arraystruct* @unsorted_array_2, i64 0, i64 11)
  call void @bubblesort(%arraystruct* @unsorted_array_3, i64 0, i64 11)
  call void @bubblesort(%arraystruct* @unsorted_array_4, i64 0, i64 11)
  call void @bubblesort(%arraystruct* @unsorted_array_5, i64 0, i64 11)

  %return_val_1 = call i1 @is_sorted(%arraystruct* @unsorted_array_1)
  %return_val_2 = call i1 @is_sorted(%arraystruct* @unsorted_array_2)
  %return_val_3 = call i1 @is_sorted(%arraystruct* @unsorted_array_5)
  %return_val_4 = call i1 @is_sorted(%arraystruct* @unsorted_array_4)
  %return_val_5 = call i1 @is_sorted(%arraystruct* @unsorted_array_3)

  %ret = add i64 %return_val_1, %return_val_2
  %ret = add i64 %ret, %return_val_3
  %ret = add i64 %ret, %return_val_4
  %ret = add i64 %ret, %return_val_5

  ret i1 %ret
}
