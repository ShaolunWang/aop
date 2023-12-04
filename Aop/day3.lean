import Mathlib
import Std.Tactic.RCases
import Std.Data.List.Lemmas

@[aesop unsafe]
inductive subseq {A : Type} : List A → List A → Prop where 
| subseq_nil : subseq [] []
| subseq_cons : ∀{xs ys}{x}, subseq xs ys → subseq (x :: xs) (x :: ys)
| subseq_skip : ∀{x}{xs ys}, subseq xs ys → subseq xs (x :: ys)
infix:50 " ⊑ " => subseq

@[aesop safe, simp, refl]
theorem subseq_refl : ∀{A : Type} (xs : List A), xs ⊑ xs := by
  intros A xs
  induction xs
  . apply subseq.subseq_nil
  . rename_i head tail tail_ih
    apply subseq.subseq_cons
    assumption

@[aesop safe, simp]
theorem subseq_empty {A : Type}(xs : List A) : [] ⊑ xs := by
  induction xs
  . apply subseq_refl
  . rename_i head tail tail_ih
    apply subseq.subseq_skip
    simp_all only
    
@[aesop safe, simp]
theorem subseq_empty_ys {A : Type}(xs: List A) : xs ⊑ [] → xs = [] := by
  intros h
  induction xs
  . trivial
  . simp_all only
    contradiction


@[aesop safe, simp]
theorem subseq_same_tail {A : Type} (head : A) (tail : List A) : tail ⊑ head :: tail := by
  cases tail with
  | nil => apply subseq_empty
  | cons =>
    rename_i h t
    apply subseq.subseq_skip
    apply subseq.subseq_cons
    apply subseq_refl



@[aesop safe, simp]
theorem subseq_tail_cons {A : Type}(h : A)(xs ys : List A) :  h :: xs ⊑ ys → xs ⊑ ys := by
  intro h'
  induction xs
  . simp_all only [subseq_refl, subseq_empty]
  . rename_i hp t t_ih
    sorry
    


--@[aesop safe, simp]
/- theorem subseq_same_tail_what {A : Type}(head : A) (t: List A)(tail : List A) : head :: t ⊑ tail → t ⊑ tail := by
  intro h
  induction t
  . simp_all only [subseq_refl, subseq_empty]
  . induction tail
    case nil =>
      rename_i h' t tail_ih -/

   
theorem subseq_trans : ∀{A : Type}{xs ys zs : List A}, xs ⊑ ys → ys ⊑ zs → xs ⊑ zs := by
  intros A xs ys zs xy yz 
  induction ys
  case nil => 
    simp_all only [subseq_refl, subseq_empty, subseq_empty_ys]
  case cons =>
    rename_i h t t_ih
    apply t_ih
    case yz =>
      sorry      
    case xy =>
      sorry
      
      
    
    
theorem subseq_len : ∀{A : Type}{xs ys : List A}, xs ⊑ ys → List.length xs ≤ List.length ys := by
  intros A xs ys
  sorry

theorem subseq_antisym : ∀{A : Type}{xs ys : List A}, xs ⊑ ys → ys ⊑ xs → xs = ys := by
sorry
