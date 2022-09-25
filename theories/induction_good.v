From stdpp Require Import base.
From Coq.micromega Require Import Lia.

Lemma nat_add_0 (n : nat) :
 	n + 0 = n.
Proof.
	induction n as [|n' IHn'].
	- (* Base case의 증명. *)
		(* 우선, 덧셈의 정의에 의해 0 + 0을 0으로 쓸수 있다. *)
		simpl.
		(* 그럼 LHS = RHS이므로 자명하게 참이다 *)
		reflexivity.
	- (* Inductive case의 증명. *)
		(* 우선, 덧셈의 정의에 의해 S n' + 0을 S (n' + 0)으로 쓸수 있다. *)
		simpl.
		(* 그럼, 귀납법 가정에 의해 n' + 0은 n'으로 쓸수 있다. *)
		rewrite IHn'.
		(* 그럼 LHS = RHS이므로 자명하게 참이다 *)
		reflexivity.
Qed.