%array = type [10 x i64]

@nums = global %array [i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8, i64 9, i64 10]

define i64 @sum() {
    %ipt = alloca i64 
    store i64 0, i64* %ipt 
    %sumpt = alloca i64 
    store i64 0, i64* %sumpt 
    br label %loop
loop: 
    %i = load i64, i64* %ipt 
    %s = load i64, i64* %sumpt 
    %elempt = getelementptr %array, %array* @nums, i32 0, i64 %i 
    %elem = load i64, i64* %elempt 
    %s2 = add i64 %s, %elem
    %i2 = add i64 %i, 1 
    store i64 %s2, i64* %sumpt 
    store i64 %i2, i64* %ipt 

    %test = icmp slt i64 %i2, 10
    br i1 %test, label %loop, label %end 

end: 
    ret i64 %s2 
}

define i64 @main(i64 %argc, i8** %argv) {
    %ans = call i64 @sum()
    ret i64 %ans 
}