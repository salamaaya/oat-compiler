; Eric Zhao (PennKey zhaoer), Nathaniel Lao (PennKey nlao)

%node = type { i64, %node* }

define i1 @find_cycle_rec_helper(%node* %slow, %node* %fast) {
    %fast_is_null = icmp eq %node* %fast, null
    br i1 %fast_is_null, label %no_cycle_found, label %incr_fast

incr_fast:
    %fast_next_ptr = getelementptr %node, %node* %fast, i32 0, i32 1
    %fast_next = load %node*, %node** %fast_next_ptr
    %fast_next_is_null = icmp eq %node* %fast_next, null
    br i1 %fast_next_is_null, label %no_cycle_found, label %find_nexts

find_nexts:
    %fast_next_next_ptr = getelementptr %node, %node* %fast_next, i32 0, i32 1
    %fast_next_next = load %node*, %node** %fast_next_next_ptr
    %slow_next_ptr = getelementptr %node, %node* %slow, i32 0, i32 1
    %slow_next = load %node*, %node** %slow_next_ptr
    %pointers_equal = icmp eq %node* %fast_next_next, %slow_next
    br i1 %pointers_equal, label %cycle_found, label %recursive_call

recursive_call:
    %result = call i1 @find_cycle_rec_helper(%node* %slow_next, %node* %fast_next_next)
    ret i1 %result

cycle_found:
    ret i1 1
no_cycle_found:
    ret i1 0
}

define i1 @find_cycle(%node* %start) {
    %result = call i1 @find_cycle_rec_helper(%node* %start, %node* %start)
    ret i1 %result
}

define i1 @main(i64 %argc, i8** %argv) {
    %1 = alloca %node
    %2 = alloca %node
    %3 = alloca %node
    %4 = alloca %node
    %5 = alloca %node
    %next_ptr_1 = getelementptr %node, %node* %1, i32 0, i32 1
    %next_ptr_2 = getelementptr %node, %node* %2, i32 0, i32 1
    %next_ptr_3 = getelementptr %node, %node* %3, i32 0, i32 1
    %next_ptr_4 = getelementptr %node, %node* %4, i32 0, i32 1
    %next_ptr_5 = getelementptr %node, %node* %5, i32 0, i32 1
    br label %empty_list

empty_list:
    %empty_list_result = call i1 @find_cycle(%node* null)
    br i1 %empty_list_result, label %failure, label %singleton

singleton:
    store %node* null, %node** %next_ptr_1
    %singleton_result = call i1 @find_cycle(%node* %1)
    br i1 %singleton_result, label %failure, label %self_loop

self_loop:
    store %node* %1, %node** %next_ptr_1
    %self_loop_result = call i1 @find_cycle(%node* %1)
    br i1 %self_loop_result, label %long_no_cycle_odd, label %failure

long_no_cycle_odd:
    store %node* %2, %node** %next_ptr_1
    store %node* %3, %node** %next_ptr_2
    store %node* %4, %node** %next_ptr_3
    store %node* %5, %node** %next_ptr_4
    store %node* null, %node** %next_ptr_5
    %long_no_cycle_odd_result = call i1 @find_cycle(%node* %1)
    br i1 %long_no_cycle_odd_result, label %failure, label %two_cycle

two_cycle:
    store %node* %2, %node** %next_ptr_1
    store %node* %1, %node** %next_ptr_2
    %two_cycle_result = call i1 @find_cycle(%node* %1)
    br i1 %two_cycle_result, label %long_no_cycle_even, label %failure

long_no_cycle_even:
    store %node* %2, %node** %next_ptr_1
    store %node* %3, %node** %next_ptr_2
    store %node* %4, %node** %next_ptr_3
    store %node* null, %node** %next_ptr_4
    %long_no_cycle_even_result = call i1 @find_cycle(%node* %1)
    br i1 %long_no_cycle_even_result, label %failure, label %long_even_cycle

long_even_cycle:
    store %node* %2, %node** %next_ptr_1
    store %node* %3, %node** %next_ptr_2
    store %node* %4, %node** %next_ptr_3
    store %node* %1, %node** %next_ptr_4
    %long_even_cycle_result = call i1 @find_cycle(%node* %1)
    br i1 %long_even_cycle_result, label %long_odd_cycle, label %failure

long_odd_cycle:
    store %node* %2, %node** %next_ptr_1
    store %node* %3, %node** %next_ptr_2
    store %node* %4, %node** %next_ptr_3
    store %node* %5, %node** %next_ptr_4
    store %node* %1, %node** %next_ptr_5
    %long_odd_cycle_result = call i1 @find_cycle(%node* %1)
    br i1 %long_odd_cycle_result, label %cycle_in_middle, label %failure

cycle_in_middle:
    store %node* %2, %node** %next_ptr_1
    store %node* %3, %node** %next_ptr_2
    store %node* %4, %node** %next_ptr_3
    store %node* %5, %node** %next_ptr_4
    store %node* %3, %node** %next_ptr_5
    %cycle_in_middle_result = call i1 @find_cycle(%node* %1)
    br i1 %cycle_in_middle_result, label %success, label %failure

success:
    ret i1 0
failure:
    ret i1 1
}
