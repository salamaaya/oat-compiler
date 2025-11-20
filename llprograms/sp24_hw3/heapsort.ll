%arraystruct = type {[9 x i64]}

; 8,7,2,1,0,9,3,2,1
@gtest1 = global %arraystruct {[9 x i64] [i64 8, i64 7, i64 2, i64 1, i64 0, i64 9, i64 3, i64 2, i64 1]}
@ans1 = global %arraystruct {[9 x i64] [i64 0, i64 1, i64 1, i64 2, i64 2, i64 3, i64 7, i64 8, i64 9]}
@gtest2 = global %arraystruct {[9 x i64] [i64 1, i64 5, i64 3, i64 8, i64 2, i64 6, i64 9, i64 4, i64 7]}
@ans2 = global %arraystruct {[9 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8, i64 9]}
@gtest3 = global %arraystruct {[9 x i64] [i64 9, i64 3, i64 6, i64 1, i64 5, i64 2, i64 7, i64 8, i64 4]}
@ans3 = global %arraystruct {[9 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8, i64 9]}
@gtest4 = global %arraystruct {[9 x i64] [i64 5, i64 2, i64 8, i64 9, i64 1, i64 4, i64 6, i64 3, i64 7]}
@ans4 = global %arraystruct {[9 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8, i64 9]}

define i1 @eq9(%arraystruct* %arr1, %arraystruct* %arr2) {
  %lengthptr = alloca i64
  store i64 9, i64* %lengthptr
  %length = load i64, i64* %lengthptr
  %iptr = alloca i64
  store i64 0, i64* %iptr
  br label %loop_entry
loop_entry:
  %iteri = load i64, i64* %iptr
  %cmpll = icmp slt i64 %iteri, %length
  br i1 %cmpll, label %loop_body, label %loop_exit_s
loop_body:
  %arri1ptr = getelementptr %arraystruct, %arraystruct* %arr1, i32 0, i32 0, i64 %iteri
  %arri1 = load i64, i64* %arri1ptr
  %arri2ptr = getelementptr %arraystruct, %arraystruct* %arr2, i32 0, i32 0, i64 %iteri
  %arri2 = load i64, i64* %arri2ptr
  %cmp12 = icmp eq i64 %arri1, %arri2
  br i1 %cmp12, label %loop_next, label %loop_exit_f
loop_next:
  %i = load i64, i64* %iptr
  %iplus = add i64 %i, 1
  store i64 %iplus, i64* %iptr
  br label %loop_entry
loop_exit_s:
  ret i1 1
loop_exit_f:
  ret i1 0
}

define void @swap(i64* %a, i64* %b) {
  %temp = load i64, i64* %a
  %temp2 = load i64, i64* %b
  store i64 %temp2, i64* %a
  store i64 %temp, i64* %b
  ret void
}

define void @heapify(%arraystruct* %arr, i64 %N, i64 %i) {
    %largest_ptr = alloca i64
    store i64 %i, i64* %largest_ptr

    %l_ptr = alloca i64
    %heapify_1 = mul i64 %i, 2
    %heapify_2 = add i64 %heapify_1, 1
    store i64 %heapify_2, i64* %l_ptr

    %r_ptr = alloca i64
    %heapify_3 = mul i64 %i, 2
    %heapify_4 = add i64 %heapify_3, 2
    store i64 %heapify_4, i64* %r_ptr

; if (l < N && arr[l] > arr[largest])
    %l = load i64, i64* %l_ptr
    %l_cond_1 = icmp slt i64 %l, %N
    
    %arr_l_ptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %l
    %largest = load i64, i64* %largest_ptr
    %arr_largest_ptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %largest
    %arr_l = load i64, i64* %arr_l_ptr
    %arr_largest = load i64, i64* %arr_largest_ptr
    %l_cond_2 = icmp sgt i64 %arr_l, %arr_largest
    
    %l_cond_res = and i1 %l_cond_1, %l_cond_2

    br i1 %l_cond_res, label %l_update, label %r_cmp

l_update: 
    store i64 %l, i64* %largest_ptr
    br label %r_cmp

r_cmp:
; if (r < N && arr[r] > arr[largest])
    %r = load i64, i64* %r_ptr
    %r_cond_1 = icmp slt i64 %r, %N
    %arr_r_ptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %r
    %largest_2 = load i64, i64* %largest_ptr
    %heapify_5_ptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %largest_2
    %arr_r = load i64, i64* %arr_r_ptr
    %heapify_5 = load i64, i64* %heapify_5_ptr

    %r_cond_2 = icmp sgt i64 %arr_r, %heapify_5
    %r_cond_res = and i1 %r_cond_1, %r_cond_2

    br i1 %r_cond_res, label %r_update, label %check_for_swap
    
r_update: 
    store i64 %r, i64* %largest_ptr
    br label %check_for_swap

check_for_swap:
; if (largest != i)
    %largest_swap = load i64, i64* %largest_ptr
    %swap_cond = icmp ne i64 %largest_swap, %i

    br i1 %swap_cond, label %do_swap, label %exit

do_swap:
    %arr_i_ptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %i
    %largest_3 = load i64, i64* %largest_ptr
    %arr_largest_ptr_2 = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %largest_3

    %my_temp = load i64, i64* %arr_i_ptr

    call void @swap(i64* %arr_i_ptr, i64* %arr_largest_ptr_2)
    call void @heapify(%arraystruct* %arr, i64 %N, i64 %largest_3)
    br label %exit

exit:
  ret void

}

define void @heapsort(%arraystruct* %arr, i64 %N) {
    %1 = alloca i64 ; N
    store i64 %N, i64* %1

    %2 = lshr i64 %N, 1 ; half
    %3 = sub i64 %2, 1 ; half - 1

    %fst_loop_ptr = alloca i64
    store i64 %3, i64* %fst_loop_ptr ; ptr to half - 1
    
    %4 = sub i64 %N, 1 ; N - 1

    %snd_loop_ptr = alloca i64
    store i64 %4, i64* %snd_loop_ptr ; ptr to half - 1

    %5 = alloca i64
    store i64 0, i64* %5 ; zero, for loop comparisons
    br label %fst_loop_entry
    
fst_loop_entry:
    %loop_cond = load i64, i64* %fst_loop_ptr
    %five_temp = load i64, i64* %5
    %cmp_zero = icmp sge i64 %loop_cond, %five_temp
    br i1 %cmp_zero, label %loop_body, label %snd_loop_entry

loop_body:
    call void @heapify(%arraystruct* %arr, i64 %N, i64 %loop_cond)
    %next_iter = sub i64 %loop_cond, 1
    store i64 %next_iter, i64* %fst_loop_ptr
    br label %fst_loop_entry

snd_loop_entry:
    %snd_loop_cond = load i64, i64* %snd_loop_ptr 
    %five_temp_two = load i64, i64* %5
    %cmp_zero_two = icmp sge i64 %snd_loop_cond, %five_temp_two
    br i1 %cmp_zero_two, label %snd_loop_body, label %snd_loop_exit

snd_loop_body:
    %arr_zero_ptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 0
    %arr_n_sub_one_ptr = getelementptr %arraystruct, %arraystruct* %arr, i32 0, i32 0, i64 %snd_loop_cond
    call void @swap(i64* %arr_zero_ptr, i64* %arr_n_sub_one_ptr)
    %call_five_val = load i64, i64* %5
    call void @heapify(%arraystruct* %arr, i64 %snd_loop_cond, i64 %call_five_val)

    %snd_next_iter = sub i64 %snd_loop_cond, 1
    store i64 %snd_next_iter, i64* %snd_loop_ptr
    br label %snd_loop_entry

snd_loop_exit:
    ret void
}

define i1 @main(i64 %argc, i8** %arcv) {
    call void @heapsort(%arraystruct* @gtest1, i64 9)
    %res1 = call i1 @eq9(%arraystruct* @gtest1, %arraystruct* @ans1)
    call void @heapsort(%arraystruct* @gtest2, i64 9)
    %res2 = call i1 @eq9(%arraystruct* @gtest2, %arraystruct* @ans2)
    call void @heapsort(%arraystruct* @gtest3, i64 9)
    %res3 = call i1 @eq9(%arraystruct* @gtest3, %arraystruct* @ans3)
    call void @heapsort(%arraystruct* @gtest4, i64 9)
    %res4 = call i1 @eq9(%arraystruct* @gtest4, %arraystruct* @ans4)
    %resagg1 = and i1 %res1, %res2
    %resagg2 = and i1 %resagg1, %res3
    %resagg3 = and i1 %resagg2, %res4
    
    ret i1 %resagg3
}