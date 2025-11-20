%arr = type [5 x i64]

@glb_arr = global %arr [i64 1, i64 1, i64 4, i64 3, i64 3]

define  i64 @singleNumber(%arr* %myarr, i64 %size)
{
  %result  = alloca i64 
  store i64 0, i64* %result

  %index = alloca i64
  store i64 0, i64* %index

  br label %loop
loop:
  %l_idx  = load i64, i64* %index
  %idx_check = icmp slt i64 %l_idx, %size
  br i1 %idx_check, label %compute, label %ret_ext

compute:
  %compute_index = load i64, i64* %index
  %elem = getelementptr %arr, %arr* %myarr, i32 0, i32 %compute_index
  %new_elem = load i64, i64* %elem
  %temp_res = load i64, i64* %result
  %new_res = xor i64 %new_elem, %temp_res
  store i64 %new_res, i64* %result

  br label %loop_inc

loop_inc: 
  %inc_idx  = load i64, i64* %index
  %new_idx = add i64 %inc_idx, 1
  store i64 %new_idx, i64* %index
  br label %loop

ret_ext:
  %return_val = load i64, i64* %result
  ret i64 %return_val
}

define i64 @main(i64 %argc, i8** %argv){
  ; Expected Return Value 4
  ; This function XORs the elements of the array to find single unique element
  ; Second argument is size of the array
  %ans = call i64 @singleNumber(%arr* @glb_arr, i64 5)
  ret i64 %ans
}


