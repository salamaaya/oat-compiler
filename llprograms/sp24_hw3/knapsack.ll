; 0/1 Knapsack Problem (Recursive solution)
;   * Input: array of weights, array of values, and a capacity of a knapsack
;   * Output: the maximum value that can be obtained by selecting items,
;     while keeping the total weight within the capacity of the knapsack.

; operates on a struct of an array
; uses recursion
; one helper function with use of call instruction

%arraystruct = type { [5 x i64] }

; Test 1: Basic functionality / correctness

@weights1 = global %arraystruct {[5 x i64] [i64 2, i64 3, i64 4, i64 5, i64 6]}
@values1 = global %arraystruct {[5 x i64] [i64 3, i64 4, i64 5, i64 6, i64 7]}
@capacity1 = global i64 5

@expected1 = global i64 7

; Test 2: Balance between maximizing the value and staying within the capacity limit

@weights2 = global %arraystruct {[5 x i64] [i64 1, i64 2, i64 3, i64 4, i64 5]}
@values2 = global %arraystruct {[5 x i64] [i64 1, i64 3, i64 4, i64 5, i64 6]}
@capacity2 = global i64 8

@expected2 = global i64 10

; Test 3: Lower weights have higher values

@weights3 = global %arraystruct {[5 x i64] [i64 5, i64 4, i64 3, i64 2, i64 1]}
@values3 = global %arraystruct {[5 x i64] [i64 6, i64 5, i64 4, i64 3, i64 2]}
@capacity3 = global i64 10

@expected3 = global i64 14


define i64 @knapsack(i64 %n, %arraystruct* %weights, %arraystruct* %values, i64 %capacity) {
    ; %n_minus_1 = sub i64 %n, 1
    ; %1 = getelementptr %arraystruct, %arraystruct* %weights, i32 0, i32 0, i64 %n_minus_1
    ; %2 = load i64, i64* %1
    ; ret i64 %2

    %is_n_0 = icmp eq i64 %n, 0
    %is_n_1 = icmp eq i64 %capacity, 0
    %base_case = or i1 %is_n_0, %is_n_1
    br i1 %base_case, label %base_case_end, label %continue1

    base_case_end:
    ret i64 0

    continue1:
    %n_minus_1 = sub i64 %n, 1
    %w_n_minus_1_ptr = getelementptr %arraystruct, %arraystruct* %weights, i32 0, i32 0, i64 %n_minus_1
    %w_n_minus_1 = load i64, i64* %w_n_minus_1_ptr

    %2 = icmp sgt i64 %w_n_minus_1, %capacity
    br i1 %2, label %recursive_case1, label %continue2

    recursive_case1:
    %knapsack_with_n_minus_1 = call i64 @knapsack(i64 %n_minus_1, %arraystruct* %weights, %arraystruct* %values, i64 %capacity)
    ret i64 %knapsack_with_n_minus_1
 
    continue2:

    %val_at_n_minus_1_ptr = getelementptr %arraystruct, %arraystruct* %values, i32 0, i32 0, i64 %n_minus_1
    %val_at_n_minus_1 = load i64, i64* %val_at_n_minus_1_ptr

    %new_capacity = sub i64 %capacity, %w_n_minus_1
    %knapsack_with_n_minus_1_new_capacity = call i64 @knapsack(i64 %n_minus_1, %arraystruct* %weights, %arraystruct* %values, i64 %new_capacity)
    %left_for_max = add i64 %val_at_n_minus_1, %knapsack_with_n_minus_1_new_capacity
    %right_for_max = call i64 @knapsack(i64 %n_minus_1, %arraystruct* %weights, %arraystruct* %values, i64 %capacity)
 

    %max = icmp sgt i64 %left_for_max, %right_for_max
    br i1 %max, label %include_item, label %dont_include_item

    include_item:
    ret i64 %left_for_max

    dont_include_item:
    ret i64 %right_for_max
}

define void @main(i64 %argc, i8** %arcv) {
  ; get result of Test 1
    %ptr_weights1 = getelementptr %arraystruct, %arraystruct* @weights1, i32 0
    %ptr_values1 = getelementptr %arraystruct, %arraystruct* @values1, i32 0
    %capacity1_val = load i64, i64* @capacity1
    %res1 = call i64 @knapsack(i64 5, %arraystruct* %ptr_weights1, %arraystruct* %ptr_values1, i64 %capacity1_val)

    ; whether Test 1 passed or not (i1)
    %expected1_val = load i64, i64* @expected1
    %res1_pass = icmp eq i64 %res1, %expected1_val


  ; get result of Test 2
    %ptr_weights2 = getelementptr %arraystruct, %arraystruct* @weights2, i32 0
    %ptr_values2 = getelementptr %arraystruct, %arraystruct* @values2, i32 0
    %capacity2_val = load i64, i64* @capacity2
    %res2 = call i64 @knapsack(i64 5, %arraystruct* %ptr_weights2, %arraystruct* %ptr_values2, i64 %capacity2_val)

  ; whether Test 2 passed or not (i1)
    %expected2_val = load i64, i64* @expected2
    %res2_pass = icmp eq i64 %res2, %expected2_val

    

  ; get result of Test 3
    %ptr_weights3 = getelementptr %arraystruct, %arraystruct* @weights3, i32 0
    %ptr_values3 = getelementptr %arraystruct, %arraystruct* @values3, i32 0
    %capacity3_val = load i64, i64* @capacity3
    %res3 = call i64 @knapsack(i64 5, %arraystruct* %ptr_weights3, %arraystruct* %ptr_values3, i64 %capacity3_val)

  ; whether Test 3 passed or not (i1)
    %expected3_val = load i64, i64* @expected3
    %res3_pass = icmp eq i64 %res3, %expected3_val



    ; return 1 if all tests passed
    %res1_and_res2_pass = and i1 %res1_pass, %res2_pass
    %all_pass = and i1 %res1_and_res2_pass, %res3_pass
    ret i64 %all_pass
}
