From stdpp Require Import base gmultiset fin_sets.

(* 공집합이 아닌 집합은 크기가 0보다 크다는 보조정리  *)
Lemma non_empty_pos (X : gmultiset nat) n :
  n ∈ X → size X > 0.
Proof.
  intros. assert (size X ≠ 0); [|lia].
  intros Size.
  apply gmultiset_size_empty_iff in Size.
  set_solver.
Qed.

Lemma single_elem_of_gmultiset (X : gmultiset nat) n m :
  n ∈ X ⊎ {[+ m +]} →
  1 = size (X ⊎ {[+ m +]}) →
  n = m.
Proof.
  intros n_in Hs.
  rewrite gmultiset_size_disj_union in Hs.
  rewrite gmultiset_size_singleton in Hs.
  assert (X = ∅) as ->.
  { apply gmultiset_size_empty_iff. lia. }
  rewrite gmultiset_disj_union_left_id in n_in.
  by apply gmultiset_elem_of_singleton.
Qed.

Lemma one_gmultiset_not_empty (X : gmultiset nat) n :
  size X > 1 → n ∈ X → X ∖ {[+ n +]} ≠ ∅.
Proof.
  intros. rewrite <-gmultiset_size_empty_iff. intros Zero.
  rewrite gmultiset_size_difference in Zero; [|multiset_solver].
  rewrite gmultiset_size_singleton in Zero. lia.
Qed.

Lemma fake_set_eq (X : gmultiset nat) n m:
    n ∈ X ⊎ {[+ m +]} → n = m.
Proof.
  set (Y := X ⊎ {[+ m +]}).
  (* n ∈ X라는 사실과 귀납변수가 될 집합의 크기 m을 소개. *)
  intro n_in. remember (size Y) as s eqn:Hs.
  (* 보조정리로 크기가 0보다 크다는 사실을 암. *)
  assert (s > 0) as s_pos by (subst s; by apply (non_empty_pos (X ⊎ {[m]}) n)).
  (* 귀납 시작. *)
  induction s as [|s' IHs'].
  - (* Base Case. Vacuously true. *)
    inversion s_pos.
  - (* Inductive Case. *)
    destruct (decide (s' = 0)) as [->|Gt].
    (* 우선 s' = 0일때를 후딱 치우자. *)
    { by apply (single_elem_of_gmultiset X n m). }
    (* 그럼 S s' > 1임. *)
    assert (S s' > 1) by lia.
    (* 우선 p₁을 얻기 위해 공집합이 아님을 보임 *)
    assert (Y ≠ ∅) as NotEmpty.
    { (* 자명함. *) multiset_solver. }
    (* p₁ 얻기 성공! *)
    apply gmultiset_choose in NotEmpty;
    destruct NotEmpty as [p₁ p₁_in].
    (* 이제 다른 원소 p₂를 얻어야함 *)
    assert (Y ∖ {[+ p₁ +]} ≠ ∅) as NotEmpty.
    { (* 크기가 1보다 크니 자명함. *) apply (one_gmultiset_not_empty Y p₁); [lia|done]. }
    (* p₂ 얻기 성공! *)
    apply gmultiset_choose in NotEmpty;
    destruct NotEmpty as [p₂ p₂_in].
    (* 교집합에서 원소가 있음을 보이기 위해, 교집합이 공집합이 아님을 증명해보자... *)
    assert ((Y ∖ {[+ p₁ +]}) ∩ (Y ∖ {[+ p₂ +]}) ≠ ∅) as NonEmpty.
    { (* 할수 있는게 없다!!! *) admit. }
Abort.

