
; Created by Adam & Hassan :)
; Finds a duplicate to the array assuming there is only one duplicate and all items are in range [1, n]

; LeetCode #287
; Given an array of integers nums containing n + 1 integers where each integer is in the range [1, n] inclusive.
; There is only one repeated number in nums, return this repeated number.
; You must solve the problem without modifying the array nums and uses only constant extra space.
; Uses Floyd's Cycle Detection algo

%arr_t = type [5 x i64]
@input_arr = global %arr_t [ i64 1, i64 2, i64 3, i64 3, i64 4 ]


define i64 @find_dup() {

    ; initialize my slow and fast pointers
    %slow = alloca i64 
    %fast = alloca i64

    ; second slow pointer for phase 2
    %slow_2 = alloca i64

    ; set them all to 0
    store i64 0, i64* %slow
    store i64 0, i64* %fast
    store i64 0, i64* %slow_2

    ; move on
    br label %phase_1_loop

phase_1_loop:
    ; slow = nums[slow]
    ; aka stepping through slow
    %slow_val = load i64, i64* %slow
    %slow_val_ptr = getelementptr %arr_t, %arr_t* @input_arr, i64 0, i64 %slow_val
    %slow_val_loaded = load i64, i64* %slow_val_ptr
    store i64 %slow_val_loaded, i64* %slow

    ; fast = nums[nums[fast]]
    ; aka stepping through fast
    %fast_val = load i64, i64* %fast
    %fast_val_ptr = getelementptr %arr_t, %arr_t* @input_arr, i64 0, i64 %fast_val
    %fast_val_loaded = load i64, i64* %fast_val_ptr
    %fast_val_ptr_2 = getelementptr %arr_t, %arr_t* @input_arr, i64 0, i64 %fast_val_loaded
    %fast_val_loaded2 = load i64, i64* %fast_val_ptr_2
    store i64 %fast_val_loaded2, i64* %fast

    ; if slow == fast, break
    ; otherwise, continue
    %cmp = icmp eq i64 %slow_val_loaded, %fast_val_loaded2
    br i1 %cmp, label %phase_2_loop, label %phase_1_loop

phase_2_loop:
    ; slow = nums[slow]
    ; aka stepping through slow
    %slow_val_p2 = load i64, i64* %slow
    %slow_val_ptr_p2 = getelementptr %arr_t, %arr_t* @input_arr, i64 0, i64 %slow_val_p2
    %slow_val_p2_2 = load i64, i64* %slow_val_ptr_p2
    store i64 %slow_val_p2_2, i64* %slow

    ; slow = nums[slow_2]
    ; aka stepping through other slow
    %slow2_val = load i64, i64* %slow_2
    %slow2_val_ptr_p2 = getelementptr %arr_t, %arr_t* @input_arr, i64 0, i64 %slow2_val
    %slow2_val_2 = load i64, i64* %slow2_val_ptr_p2
    store i64 %slow2_val_2, i64* %slow_2
    
    ; if slow == slow_2, return slow, otherwise loop
    %cmp_p2 = icmp eq i64 %slow_val_p2_2, %slow2_val_2
    br i1 %cmp, label %return_slow, label %phase_2_loop

return_slow:
    ret i64 %slow_val_p2_2
}


; just takes in the global arr - to avoid compile issues
; should return 3L
define i64 @main(i64 %argc, i8** %argv) {
    %main_result = call i64 @find_dup()
    ret i64 %main_result
}


