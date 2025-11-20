; Copied https://www.geeksforgeeks.org/longest-sub-array-sum-k/

%array = type [10 x i64]

@arr = global %array [ i64 10, i64 2, i64 7, i64 4, i64 1, i64 2, i64 3, i64 1, i64 1, i64 4 ]
@arr_len = global i64 10
@my_k = global i64 12

define i64 @lenOfLongSubarr(i64* %arr, i64 %N, i64 %K) {

entry:
  ; maxlength = 0
  %maxlength = alloca i64 
  store i64 0, i64* %maxlength  
  %i = alloca i64
  ; Initialize i = 0
  store i64 0, i64* %i
  br label %outer_loop

outer_loop:
  %i_val = load i64, i64* %i
  ; is i < N?
  %cmp1 = icmp slt i64 %i_val, %N
  ; if yes, move into inner loop ; else, end outer loop
  br i1 %cmp1, label %inner_loop_entry, label %outer_loop_end

inner_loop_entry:
  %Sum = alloca i64
  ; Sum = 0
  store i64 0, i64* %Sum
  %j = alloca i64
  ; Initialize j = i
  store i64 %i_val, i64* %j 
  br label %inner_loop

inner_loop:
  %j_val = load i64, i64* %j
  ; Is j < N?
  %cmp2 = icmp slt i64 %j_val, %N
  ; If it is, jump to loop body; else, end inner loop
  br i1 %cmp2, label %loop_body, label %inner_loop_end

loop_body:
  %Sum_val = load i64, i64* %Sum
  ; get arr[j]
  %arr_elem = getelementptr i64, i64* %arr, i64 %j_val
  %arr_val = load i64, i64* %arr_elem
  %new_Sum = add i64 %Sum_val, %arr_val
  ; Sum += arr[j]
  store i64 %new_Sum, i64* %Sum
  %Sum_eq_K = icmp eq i64 %new_Sum, %K
  br i1 %Sum_eq_K, label %update_maxlength, label %inner_loop_cont

update_maxlength:
  %maxlength_val = load i64, i64* %maxlength
  %length = sub i64 %j_val, %i_val
  %new_length = add i64 %length, 1
  %is_longer = icmp sgt i64 %new_length, %maxlength_val
  br i1 %is_longer, label %store_maxlength, label %inner_loop_cont

store_maxlength:
  store i64 %new_length, i64* %maxlength
  br label %inner_loop_cont
  
inner_loop_cont:
  %j_inc = add i64 %j_val, 1
  ; j = j + 1
  store i64 %j_inc, i64* %j
  br label %inner_loop

inner_loop_end:
  %i_inc = add i64 %i_val, 1
  ; i = i + 1
  store i64 %i_inc, i64* %i
  br label %outer_loop

outer_loop_end:
  %maxlength_ret = load i64, i64* %maxlength
  ret i64 %maxlength_ret
}

define i64 @main(i64 %argc, i8** %argv) {
  %size_ptr = getelementptr i64, i64* @arr_len, i64 0
  %arr_size = load i64, i64* %size_ptr

  %my_k_ptr = getelementptr i64, i64* @my_k, i64 0
  %my_k_val = load i64, i64* %my_k_ptr 

  %my_res = call i64 @lenOfLongSubarr(%array* @arr, i64 %arr_size, i64 %my_k_val)
  ret i64 %my_res
}