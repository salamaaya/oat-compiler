; Merge two sorted array inplace and put the sorted array in nums1 

%first_arr_t = type [10 x i64]
%second_arr_t = type [5 x i64]

@first_arr = global %first_arr_t [i64 1, i64 2, i64 3, i64 4, i64 5, i64 0, i64 0, i64 0, i64 0, i64 0]
@second_arr = global %second_arr_t [i64 2, i64 4, i64 5, i64 8, i64 9]
@expected_arr = global %first_arr_t [i64 1, i64 2, i64 2, i64 3, i64 4, i64 4, i64 5, i64 5, i64 8, i64 9]

@first_arr2 = global %first_arr_t [i64 1, i64 1, i64 1, i64 2, i64 2, i64 0, i64 0, i64 0, i64 0, i64 0]
@second_arr2 = global %second_arr_t [i64 4, i64 4, i64 5, i64 5, i64 10]
@expected_arr2 = global %first_arr_t [i64 1, i64 1, i64 1, i64 2, i64 2, i64 4, i64 4, i64 5, i64 5, i64 10]

@first_arr3 = global %first_arr_t [i64 1, i64 2, i64 3, i64 4, i64 5, i64 0, i64 0, i64 0, i64 0, i64 0]
@second_arr3 = global %second_arr_t [i64 0, i64 0, i64 0, i64 0, i64 0]
@expected_arr3 = global %first_arr_t [i64 0, i64 0, i64 0, i64 0, i64 0, i64 1, i64 2, i64 3, i64 4, i64 5]

@first_arr4 = global %first_arr_t [i64 3, i64 3, i64 3, i64 3, i64 3, i64 0, i64 0, i64 0, i64 0, i64 0]
@second_arr4 = global %second_arr_t [i64 3, i64 3, i64 3, i64 3, i64 3]
@expected_arr4 = global %first_arr_t [i64 3, i64 3, i64 3, i64 3, i64 3, i64 3, i64 3, i64 3, i64 3, i64 3]

@first_arr5 = global %first_arr_t [i64 7, i64 8, i64 9, i64 9, i64 10, i64 0, i64 0, i64 0, i64 0, i64 0]
@second_arr5 = global %second_arr_t [i64 10, i64 11, i64 13, i64 13, i64 15]
@expected_arr5 = global %first_arr_t [i64 7, i64 8, i64 9, i64 9, i64 10, i64 10, i64 11, i64 13, i64 13, i64 15]

define i1 @is_equal(%first_arr_t* %nums1, %first_arr_t* %expected_nums1) {
  %i_ptr = alloca i64 
  store i64 0, i64* %i_ptr
  br label %for_condition

for_condition:
  %i = load i64, i64* %i_ptr
  %cmp = icmp slt i64 %i, 10
  br i1 %cmp, label %for_body, label %success

for_body:
  %nums1_i_ptr = getelementptr %first_arr_t, %first_arr_t* %nums1, i32 0, i64 %i
  %expected_nums1_i_ptr = getelementptr %first_arr_t, %first_arr_t* %expected_nums1, i32 0, i64 %i
  %nums1_i = load i64, i64* %nums1_i_ptr  
  %expected_nums1_i = load i64, i64* %expected_nums1_i_ptr  
  %cmp2 = icmp eq i64 %nums1_i, %expected_nums1_i
  br i1 %cmp2, label %continue, label %fail

continue:
  %i2 = load i64, i64* %i_ptr
  %i_plus_1 = add i64 %i2, 1
  store i64 %i_plus_1, i64* %i_ptr 
  br label %for_condition 

fail:
  ret i1 0
success:
  ret i1 1
}

define void @merge_sorted(%first_arr_t* %nums1, i64 %m, %second_arr_t* %nums2, i64 %n) {
  %i_ptr = alloca i64
  %j_ptr = alloca i64
  %k_ptr = alloca i64
  %i = add i64 %m, -1 
  %j = add i64 %n, -1
  %m_and_n = add i64 %m, %n 
  %k = add i64 %m_and_n, -1 
  store i64 %i, i64* %i_ptr
  store i64 %j, i64* %j_ptr
  store i64 %k, i64* %k_ptr
  br label %while

while:
  %curr_j = load i64, i64* %j_ptr
  %is_greater_or_equal_0 = icmp sge i64 %curr_j, 0 
  br i1 %is_greater_or_equal_0, label %check_i_greater_or_equal_0, label %done

check_i_greater_or_equal_0:
  %curr_i = load i64, i64* %i_ptr 
  %is_greater_or_equal_0_2 = icmp sge i64 %curr_i, 0
  br i1 %is_greater_or_equal_0_2, label %num_comparison, label %nums2_greater

num_comparison:
  %i_for_num = load i64, i64* %i_ptr
  %j_for_num = load i64, i64* %j_ptr
  %nums1_i_ptr = getelementptr %first_arr_t, %first_arr_t* %nums1, i32 0, i64 %i_for_num
  %nums2_j_ptr = getelementptr %second_arr_t, %second_arr_t* %nums2, i32 0, i64 %j_for_num
  %nums1_i = load i64, i64* %nums1_i_ptr 
  %nums2_j = load i64, i64* %nums2_j_ptr
  %is_nums1_greater = icmp sgt i64 %nums1_i, %nums2_j
  br i1 %is_nums1_greater, label %nums1_greater, label %nums2_greater

nums1_greater:
  %k_for_num = load i64, i64* %k_ptr
  %i_for_num2 = load i64, i64* %i_ptr
  %nums1_k_ptr = getelementptr %first_arr_t, %first_arr_t* %nums1, i32 0, i64 %k_for_num
  %nums1_i_ptr2 = getelementptr %first_arr_t, %first_arr_t* %nums1, i32 0, i64 %i_for_num2
  %nums2_i = load i64, i64* %nums1_i_ptr2
  store i64 %nums2_i, i64* %nums1_k_ptr
  %k_minus_1 = add i64 %k_for_num, -1
  %i_minus_1 = add i64 %i_for_num2, -1 
  store i64 %k_minus_1, i64* %k_ptr
  store i64 %i_minus_1, i64* %i_ptr
  br label %while
  
nums2_greater:
  %k_for_num2= load i64, i64* %k_ptr
  %j_for_num2 = load i64, i64* %j_ptr
  %nums1_k_ptr2 = getelementptr %first_arr_t, %first_arr_t* %nums1, i32 0, i64 %k_for_num2
  %nums2_j_ptr2 = getelementptr %second_arr_t, %second_arr_t* %nums2, i32 0, i64 %j_for_num2
  %nums2_j2 = load i64, i64* %nums2_j_ptr2
  store i64 %nums2_j2, i64* %nums1_k_ptr2
  %k_minus_1_2 = add i64 %k_for_num2, -1
  %j_minus_1 = add i64 %j_for_num2, -1 
  store i64 %k_minus_1_2, i64* %k_ptr
  store i64 %j_minus_1, i64* %j_ptr
  br label %while

done:
  ret void 
}

define i1 @main(i64 %argc, i8** %arcv) {
  call void @merge_sorted(%first_arr_t* @first_arr, i64 5, %second_arr_t* @second_arr, i64 5)
  %res1 = call i1 @is_equal(%first_arr_t* @first_arr, %first_arr_t* @expected_arr)
  call void @merge_sorted(%first_arr_t* @first_arr2, i64 5, %second_arr_t* @second_arr2, i64 5)
  %res2 = call i1 @is_equal(%first_arr_t* @first_arr2, %first_arr_t* @expected_arr2)
  call void @merge_sorted(%first_arr_t* @first_arr3, i64 5, %second_arr_t* @second_arr3, i64 5)
  %res3 = call i1 @is_equal(%first_arr_t* @first_arr3, %first_arr_t* @expected_arr3)
  call void @merge_sorted(%first_arr_t* @first_arr4, i64 5, %second_arr_t* @second_arr4, i64 5)
  %res4 = call i1 @is_equal(%first_arr_t* @first_arr4, %first_arr_t* @expected_arr4)
  call void @merge_sorted(%first_arr_t* @first_arr5, i64 5, %second_arr_t* @second_arr5, i64 5)
  %res5 = call i1 @is_equal(%first_arr_t* @first_arr5, %first_arr_t* @expected_arr5)

  %and1 = and i1 %res1, %res2
  %and2 = and i1 %and1, %res3
  %and3 = and i1 %and2, %res4
  %and4 = and i1 %and3, %res5
  
  ret i1 %and4
}