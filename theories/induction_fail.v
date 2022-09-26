From stdpp Require Import base gmultiset fin_sets.
From Coq Require Import ssreflect.

(* 공집합이 아닌 집합은 크기가 0보다 크다는 보조정리  *)
Lemma non_empty_pos (X : gmultiset nat) n :
  n ∈ X → size X > 0.
Proof.
  intros. assert (size X ≠ 0); [|lia].
  apply gmultiset_size_non_empty_iff. multiset_solver.
Qed.

Lemma gm_size_singleton_inv (X : gmultiset nat) n m :
  size X = 1 →
  n ∈ X → m ∈ X  →
  n = m.
Proof.
  intros HX n_in m_in.
  apply (gmultiset_disj_union_difference' m),(f_equal size) in m_in.
  rewrite HX gmultiset_size_disj_union gmultiset_size_singleton in m_in.
  assert (X ∖ {[+ m +]} = ∅) as Hm_empty.
  { apply gmultiset_size_empty_iff. lia. }
  assert (X = {[+ m +]}) as -> by multiset_solver.
  by apply gmultiset_elem_of_singleton.
Qed.

Lemma one_gmultiset_not_empty (X : gmultiset nat) n :
  size X > 1 → n ∈ X → X ∖ {[+ n +]} ≠ ∅.
Proof.
  intros.
  rewrite -gmultiset_size_empty_iff gmultiset_size_difference; [multiset_solver|].
  rewrite gmultiset_size_singleton. lia.
Qed.

Lemma apply_induction (P : gmultiset nat) p s P' :
  (∀ (m n : nat) (P : gmultiset nat),
    P ≠ ∅ → m ∈ P → n ∈ P → s = size P → n = m) →
  s > 0 →
  S s = size P →
  p ∈ P →
  P' = P ∖ {[+ p +]} →
  ∃ m, ∀ (n : nat), n ∈ P' → n = m.
Proof.
  intros IHs' ?? p_in HP'.
  assert (s = size P').
  { apply (f_equal size) in HP'. rewrite gmultiset_size_difference in HP'; [multiset_solver|].
    rewrite gmultiset_size_singleton in HP'. lia.
  }
  destruct (gmultiset_choose P') as [m m_in].
  { apply gmultiset_size_non_empty_iff. lia. }
  exists m. intros n n_in. apply (IHs' m n P'); [multiset_solver|done..].
Qed.

Lemma fake_set_eq (P : gmultiset nat) n :
    P ≠ ∅ → ∃ m, n ∈ P → n = m.
Proof.
  intros NotEmpty.
  destruct (gmultiset_choose P) as [m m_in]; [done|].
  exists m.
  (* n ∈ X라는 사실과 귀납변수가 될 집합의 크기 m을 소개. *)
  intro n_in. remember (size P) as N eqn:HN.
  (* 보조정리로 크기가 0보다 크다는 사실을 암. *)
  assert (N > 0) as N_pos by (subst N; by apply (non_empty_pos P n)).
  (* 올바른 induction hypothesis을 얻기 위한 작업. *)
  generalize dependent P. generalize dependent n. generalize dependent m.
  (* 귀납 시작. *)
  induction N as [|N' IHN'].
  - (* Base Case. Vacuously true. *)
    inversion N_pos.
  - (* Inductive Case. *)
    (* 우선 N = 1일때를 해결하자. *)
    destruct (decide (N' = 0)) as [->|Gt]; intros m n P NotEmpy m_in n_in HN'.
    { apply (gm_size_singleton_inv P n m); [lia|done..]. }
    (* 그럼 N > 1이다. *)
    assert (N' > 0) as Pos by lia;
    specialize (IHN' Pos). clear Pos N_pos.

    (* 우선 p1을 얻기 위해 공집합이 아님을 보임 *)
    assert (P ≠ ∅) as NotEmpty.
    { (* 자명함. *) multiset_solver. }
    (* p1 얻기 성공! *)
    apply gmultiset_choose in NotEmpty;
    destruct NotEmpty as [p1 p1_in].
    (* [P ∖ {[+ p1 +]}]에 대해 IHs' 적용. *)
    remember (P ∖ {[+ p1 +]}) as P1 eqn:HP1.
    assert (∃ m1, ∀ (n1 : nat), n1 ∈ P1 → n1 = m1) as P1_all_same.
    { apply (apply_induction P p1 N'); auto with lia. }

    (* 이제 다른 원소 p2를 얻어야함 *)
    assert (P ∖ {[+ p1 +]} ≠ ∅) as NotEmpty.
    { (* 크기가 1보다 크니 자명함. *) apply (one_gmultiset_not_empty P p1); [lia|done]. }
    (* p2 얻기 성공! *)
    apply gmultiset_choose in NotEmpty;
    destruct NotEmpty as [p2 p2_in].

    (* [P ∖ {[+ p2 +]}]에 대해 IHs' 적용. *)
    remember (P ∖ {[+ p2 +]}) as P2 eqn:HP2.
    assert (∃ m2, ∀ (n2 : nat), n2 ∈ P2 → n2 = m2) as P2_all_same.
    { apply (apply_induction P p2 N'); auto with lia. multiset_solver. }

    (* 교집합에서 원소가 있음을 보이기 위해, 교집합이 공집합이 아님을 증명해보자... *)
    assert (P1 ∩ P2 ≠ ∅) as NonEmpty.
    { subst.
      (* 여태까지와 같이 크기를 사용하자. *)
      apply gmultiset_size_non_empty_iff.
      (* 크기가... 0일수가 있네...? *)
      admit.
    }
Abort.
