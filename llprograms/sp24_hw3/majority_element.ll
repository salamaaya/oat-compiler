@test1 = global [10 x i64] [ i64 5, i64 1, i64 5, i64 2, i64 3, i64 4, i64 5, i64 5, i64 5, i64 5 ]
@test2 = global [10 x i64] [ i64 2, i64 1, i64 2, i64 2, i64 2, i64 4, i64 2, i64 5, i64 5, i64 2 ]
@test3 = global [3 x i64] [ i64 3, i64 4, i64 3 ]
@test4 = global [1 x i64] [ i64 3 ]
@test5 = global [6 x i64] [ i64 -1, i64 -1, i64 3, i64 5, i64 -1, i64 -1 ]
@test6 = global [7 x i64] [ i64 2, i64 2, i64 1, i64 1, i64 1, i64 2, i64 2 ]

define i64 @at([0 x i64]* %arr, i64 %idx) {
    %address = getelementptr [0 x i64], [0 x i64]* %arr, i32 0, i64 %idx
    %val = load i64, i64* %address
    ret i64 %val
}

define i64 @majority([0 x i64]* %arr, i64 %l, i64 %r) {
    %cmp1 = icmp eq i64 %l, %r
    br i1 %cmp1, label %base, label %label1
label1:
    %tmp1 = add i64 %l, %r
    %midpoint = ashr i64 %tmp1, 1
    %mp1 = add i64 1, %midpoint
    %recleft = call i64 @majority([0 x i64]* %arr, i64 %l, i64 %midpoint)
    %recright = call i64 @majority([0 x i64]* %arr, i64 %mp1, i64 %r)
    br label %recresults
recresults:
    %cmp2 = icmp eq i64 %recleft, %recright
    br i1 %cmp2, label %retleft, label %label2
label2:
    %leftcntptr = alloca i64
    %rightcntptr = alloca i64
    %loopvarptr = alloca i64
    store i64 0, i64* %leftcntptr
    store i64 0, i64* %rightcntptr
    store i64 %l, i64* %loopvarptr
    br label %loopconditions
loopconditions:
    %loopvar = load i64, i64* %loopvarptr
    %cmploop = icmp sgt i64 %loopvar, %r
    br i1 %cmploop, label %loopend, label %loopbody
loopbody:
    %currval = call i64 @at([0 x i64]* %arr, i64 %loopvar)
    br label %left
left:
    %cmpleft = icmp eq i64 %currval, %recleft
    br i1 %cmpleft, label %incrleft, label %right
incrleft:
    %leftcnt = load i64, i64* %leftcntptr
    %leftcntplus = add i64 1, %leftcnt
    store i64 %leftcntplus, i64* %leftcntptr
    br label %right
right:
    %cmpright = icmp eq i64 %currval, %recright
    br i1 %cmpright, label %incrright, label %loopincr
incrright:
    %rightcnt = load i64, i64* %rightcntptr
    %rightcntplus = add i64 1, %rightcnt
    store i64 %rightcntplus, i64* %rightcntptr
    br label %loopincr
loopincr:
    %loopvarforincr = load i64, i64* %loopvarptr
    %loopvarincr = add i64 1, %loopvarforincr
    store i64 %loopvarincr, i64* %loopvarptr
    br label %loopconditions
loopend:
    %cmpret = icmp sge i64 %leftcnt, %rightcnt
    br i1 %cmpret, label %retleft, label %retright
retleft:
    ret i64 %recleft
retright:
    ret i64 %recright
base:
    %retb = call i64 @at([0 x i64]* %arr, i64 %l)
    ret i64 %retb
}

define i64 @main(i64 %argc, i8** %arcv) {
    %arr1 = bitcast [10 x i64]* @test1 to [0 x i64]*
    %res1 = call i64 @majority([0 x i64]* %arr1, i64 0, i64 9)
    %cmp1 = icmp eq i64 %res1, 5
    br i1 %cmp1, label %test2, label %FAIL
test2:
    %arr2 = bitcast [10 x i64]* @test2 to [0 x i64]*
    %res2 = call i64 @majority([0 x i64]* %arr2, i64 0, i64 9)
    %cmp2 = icmp eq i64 %res2, 2
    br i1 %cmp2, label %test3, label %FAIL
test3:
    %arr3 = bitcast [3 x i64]* @test3 to [0 x i64]*
    %res3 = call i64 @majority([0 x i64]* %arr3, i64 0, i64 2)
    %cmp3 = icmp eq i64 %res3, 3
    br i1 %cmp3, label %test4, label %FAIL
test4:
    %arr4 = bitcast [1 x i64]* @test4 to [0 x i64]*
    %res4 = call i64 @majority([0 x i64]* %arr4, i64 0, i64 0)
    %cmp4 = icmp eq i64 %res4, 3
    br i1 %cmp4, label %test5, label %FAIL
test5:
    %arr5 = bitcast [6 x i64]* @test5 to [0 x i64]*
    %res5 = call i64 @majority([0 x i64]* %arr5, i64 0, i64 5)
    %cmp5 = icmp eq i64 %res5, -1
    br i1 %cmp5, label %test6, label %FAIL
test6:
    %arr6 = bitcast [7 x i64]* @test6 to [0 x i64]*
    %res6 = call i64 @majority([0 x i64]* %arr6, i64 0, i64 6)
    %cmp6 = icmp eq i64 %res6, 2
    br i1 %cmp6, label %NEXT, label %FAIL
NEXT:
    ret i64 1
FAIL:
    ret i64 0
}
