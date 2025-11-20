%struct.Tree = type { %struct.Tree*, %struct.Tree*, i64, i64 }

@test1 = global %struct.Tree { %struct.Tree* null, %struct.Tree* null, i64 1, i64 100 }
@test2 = global %struct.Tree { %struct.Tree* @test1, %struct.Tree* null, i64 2, i64 200 }
@test3 = global %struct.Tree { %struct.Tree* null, %struct.Tree* null, i64 4, i64 300 }
@test  = global %struct.Tree { %struct.Tree* @test2, %struct.Tree* @test3, i64 3, i64 400 }

@testB = global %struct.Tree { %struct.Tree* null, %struct.Tree* null, i64 1, i64 435 }
@testC = global %struct.Tree { %struct.Tree* null, %struct.Tree* null, i64 3, i64 765 }
@testA = global %struct.Tree { %struct.Tree* @testB, %struct.Tree* @testC, i64 2, i64 2356 }
@testE = global %struct.Tree { %struct.Tree* null, %struct.Tree* null, i64 5, i64 65 }
@testF = global %struct.Tree { %struct.Tree* null, %struct.Tree* null, i64 7, i64 42 }
@testD = global %struct.Tree { %struct.Tree* @testE, %struct.Tree* @testF, i64 6, i64 658 }
@testNew = global %struct.Tree { %struct.Tree* @testA, %struct.Tree* @testD, i64 4, i64 5346 }


define i64 @find_value(%struct.Tree* %t, i64 %key) {
  %1 = icmp eq %struct.Tree* %t, null
  br i1 %1, label %not_found, label %found
not_found:
  ret i64 -1
found:
  %2 = getelementptr %struct.Tree, %struct.Tree* %t, i64 0, i64 2
  %3 = load i64, i64* %2
  %4 = icmp eq i64 %3, %key
  br i1 %4, label %return_value, label %search_subtree
return_value:
  %5 = getelementptr %struct.Tree, %struct.Tree* %t, i64 0, i64 3
  %6 = load i64, i64* %5
  ret i64 %6
search_subtree:
  %7 = icmp slt i64 %key, %3
  br i1 %7, label %left_subtree, label %right_subtree
left_subtree:
  %8 = getelementptr %struct.Tree, %struct.Tree* %t, i64 0, i64 0
  %9 = load %struct.Tree*, %struct.Tree** %8
  %10 = call i64 @find_value(%struct.Tree* %9, i64 %key)
  ret i64 %10
right_subtree:
  %11 = getelementptr %struct.Tree, %struct.Tree* %t, i64 0, i64 1
  %12 = load %struct.Tree*, %struct.Tree** %11
  %13 = call i64 @find_value(%struct.Tree* %12, i64 %key)
  ret i64 %13
}

define i64 @main(i64 %argc, i8** %argv) {
  %1 = call i64 @find_value(%struct.Tree* @test, i64 1)
  %2 = call i64 @find_value(%struct.Tree* @test, i64 2)
  %3 = call i64 @find_value(%struct.Tree* @test, i64 3)
  %4 = icmp eq i64 %1, 100
  %5 = icmp eq i64 %2, 200
  %6 = icmp eq i64 %3, 400
  %7 = and i1 %4, %5
  %8 = and i1 %7, %6

  %9 = call i64 @find_value(%struct.Tree* @testNew, i64 1)
  %10 = call i64 @find_value(%struct.Tree* @testNew, i64 2)
  %11 = call i64 @find_value(%struct.Tree* @testNew, i64 3)
  %12 = call i64 @find_value(%struct.Tree* @testNew, i64 4)
  %13 = call i64 @find_value(%struct.Tree* @testNew, i64 5)
  %14 = call i64 @find_value(%struct.Tree* @testNew, i64 6)
  %15 = call i64 @find_value(%struct.Tree* @testNew, i64 7)
  %16 = icmp eq i64 %9, 435
  %17 = icmp eq i64 %10, 2356
  %18 = icmp eq i64 %11, 765
  %19 = icmp eq i64 %12, 5346
  %20 = icmp eq i64 %13, 65
  %21 = icmp eq i64 %14, 658
  %22 = icmp eq i64 %15, 42
  %23 = and i1 %16, %17
  %24 = and i1 %18, %19
  %25 = and i1 %20, %21
  %26 = and i1 %22, %23
  %27 = and i1 %24, %25
  %28 = and i1 %26, %27
  %29 = and i1 %28, %8

  br i1 %29, label %pass, label %fail
pass:
  ret i64 0
fail:
  ret i64 1
}
