(* CS516 Assertion Testing and Grading Infrastructure   *)
(* Based on UPenn CIS4521                               *)
(* Author: Steve Zdancewic                              *)

(* Do NOT modify this file -- we will overwrite it     *)
(* with our own version when testing your code.        *)

exception Timeout

(* An assertion is just a unit->unit function that either *)
(* succeeds silently or throws an Failure exception.       *)
type assertion = unit -> unit

type 'a test =
  | GradedTest of string * int * (string * 'a) list
  | Test of string * (string * 'a) list

type suite = assertion test list

(**************)
(* Assertions *)

(* Succeeds if the two given values compare equal using [=]. *)
val assert_eq : 'a -> 'a -> assertion

(* [assert_eqf f x] succeeds if [f () = x] and fails otherwise. *)
val assert_eqf : (unit -> 'a) -> 'a -> assertion

(* [assert_eqfs f x] succeeds if [f () = x] and fails with a useful error
   message otherwise. *)
val assert_eqfs : (unit -> string) -> string -> assertion

(* The always failing assertion. *)
val assert_fail : assertion

(* [timeout_assert s a] Wraps the given assertion in a timeout of [s] seconds.
   If the assertion does not complete in [s] seconds, it instead fails with a
   [Timeout] exception. *)
val timeout_assert : int -> assertion -> assertion

(* [timeout_test s t] Wraps the given test in a timeout of [s] seconds. *)
val timeout_test : int -> assertion test -> assertion test

(* [timeout_suite s suite] Wraps each test in the given test suite in a timeout
   of [s] seconds. *)
val timeout_suite : int -> suite -> suite

(***************************)
(* Generating Test Results *)

type result =
  | Pass
  | Fail of string

type outcome = result test list

val run_assertion : assertion -> result

val run_test : assertion test -> result test

val run_suite : suite -> outcome

(***********************)
(* Reporting functions *)

val result_test_to_string : string -> result test -> string

val outcome_to_string : outcome -> string
