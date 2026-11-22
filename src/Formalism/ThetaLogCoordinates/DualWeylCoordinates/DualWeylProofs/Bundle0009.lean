import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0007
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.Bundle0002

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ClosureBranching
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qr_prim {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
    (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) (I0 : TIdx mu) (hI0 : StdT I0) (d : ℤ)
    (hd : ∀ i, d ∣ ph i I0) : d ∣ 1 := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  choose q hq using hd
  have hy : ∑ i, q i • β i ∈ Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [(hS n mu hmu).2, ← hβ.2.1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
  have hcan : brk mu I0 = d • ∑ i, q i • β i := by
    rw [← hph]
    simp only [zsmul_eq_mul, Finset.mul_sum, hq, Int.cast_mul, mul_assoc]
  let c0 : {I : TIdx mu // StdT I} := ⟨I0, hI0⟩
  have h0 : ∑ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - d * r I) • brk mu I.1 = 0 := by
    have h2 : ∀ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - d * r I) • brk mu I.1 =
        (if I = c0 then brk mu I.1 else 0) - (d : GLCoord ℤ n) * (r I • brk mu I.1) := by
      intro I
      split_ifs <;> simp [zsmul_eq_mul, sub_mul, mul_assoc]
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, hr, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, ← zsmul_eq_mul]
    exact hcan
  have h1 := Fintype.linearIndependent_iff.1 (hS n mu hmu).1 _ h0 c0
  simp only [if_true] at h1
  exact ⟨r c0, by linarith⟩

lemma qr_equiv {m : ℕ} [NeZero m] {M : GLMod (m + 1)} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
    (hl : Dominant lam) (hn : Dominant nu) (hi : Interl lam nu)
    (ph : Matrix M.ι (TIdx lam) ℤ)
    (hE : (M.A * ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) : Matrix _ _ _) =
      (ph.map (Int.castRingHom (GLCoord ℤ (m + 1))) * TMat lam : Matrix _ _ _))
    {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ} (hb : IsBlock h g1 t)
    (i : M.ι) (I' : TIdx nu) :
    ∑ k, evGL h (M.A i k) * ((ph k (qr_j hi I') : ℤ) : R) =
      ((t ^ (∑ a, lam a - ∑ a, nu a) : Rˣ) : R) *
        ∑ K' : TIdx nu, ((ph i (qr_j hi K') : ℤ) : R) * evGL g1 (TMat nu K' I') := by
  have h1 := congrArg (evGL h) (congrFun (congrFun hE i) (qr_j hi I'))
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, eq_intCast, map_intCast] at h1
  rw [h1, Finset.mul_sum]
  symm
  apply Finset.sum_of_injOn (qr_j hi) (qr_j_inj hi).injOn (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  · intro K _ hK
    rw [qr_TMat_zero hb hn hi K I' (fun K' hK' => hK ⟨K', Finset.mem_coe.2 (Finset.mem_univ _), hK'⟩), mul_zero]
  · intro K' _
    rw [qr_TMat_j hb hl hn hi]
    ring

theorem closure_third_part_of (hA : LemmaA) (hS : SBasis) (hC : CntBranch) : ClosureBranching := by
  classical
  intro m _ M lam β hl hβ
  let Sg : Finset (Fin m → ℤ) :=
    (Fintype.piFinset fun a : Fin m => Finset.Icc (lam a.succ) (lam a.castSucc)).filter fun nu =>
      Dominant nu ∧ Interl lam nu
  have hSg : ∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu := by
    intro nu
    simp only [Sg, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, and_iff_right_iff_imp]
    rintro ⟨_, hi⟩ a
    exact ⟨(hi a).2, (hi a).1⟩
  have hex : ∀ I : TIdx lam, ∃ c : M.ι → ℤ, ∑ i, c i • β i = brk lam I := fun I =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (by rw [hβ.2.1]; exact Submodule.subset_span ⟨I, rfl⟩)
  choose c hc using hex
  let ph : Matrix M.ι (TIdx lam) ℤ := fun i I => c I i
  have hph : ∀ I, ∑ i, ph i I • β i = brk lam I := hc
  have hE := qc_equiv hA hS hl hβ ph hph
  refine ⟨Sg, fun nu i I' => ph i (qr_j ((hSg nu.1).1 nu.2).2 I'), hSg, ?_, ?_, ?_⟩
  · intro nu R _ h g1 t hb
    ext i I'
    exact qr_equiv hl ((hSg nu.1).1 nu.2).1 ((hSg nu.1).1 nu.2).2 ph hE hb i I'
  · intro nu
    have hpr := qr_prim hS hl hβ ph hph _ (qr_j_can_std (lam := lam) ((hSg nu.1).1 nu.2).2)
    constructor
    · intro p hp h0
      have h1 := hpr (p : ℤ) fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (congrFun h0 i)
      have h2 : p ∣ 1 := by exact_mod_cast h1
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
    · intro h0
      have h1 := hpr 0 fun i => by
        have := congrFun h0 i
        simp only [Pi.zero_apply, Int.cast_eq_zero] at this
        rw [this]
      simp at h1
  · rw [qc_card_eq hS hl hβ, hC m lam hl Sg hSg, Finset.sum_coe_sort Sg (fun nu => dMu nu)]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.CntBranch
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT gtBox)

theorem branching_count_holds : CntBranch := by
  intro m _ lam hlam Sg hSg
  have hS : Sg = gtBox lam := by
    ext nu
    rw [hSg, Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.mem_gtBox]
    constructor
    · intro h i
      exact ⟨(h.2 i).2, (h.2 i).1⟩
    · intro h
      refine ⟨Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.gtBox_anti hlam ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.mem_gtBox lam nu).2 h), fun i => ⟨(h i).2, (h i).1⟩⟩
  rw [qk_dMu_eq_dGT (m + 1) lam hlam, hS]
  show ∑ κ ∈ gtBox lam, dGT m κ = _
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT m nu (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.gtBox_anti hlam hnu)]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.CntSym
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)

lemma qk_antitone_of_step {n : ℕ} {f : Fin n → ℤ} (h : ∀ a : Fin n, ∀ h : a.1 + 1 < n, f ⟨a.1 + 1, h⟩ ≤ f a) :
    Antitone f := by
  cases n with
  | zero => intro a; exact a.elim0
  | succ m =>
    rw [Fin.antitone_iff_succ_le]
    intro i
    exact h i.castSucc (by simp)

lemma qk_hstrip_dom {n : ℕ} {nu mu : Fin n → ℤ} {b : ℕ} (h : HStrip nu mu b) : Dominant nu ∧ Dominant mu :=
  ⟨qk_antitone_of_step fun a ha => (h.1 _).trans (h.2.1 a ha),
   qk_antitone_of_step fun a ha => (h.2.1 a ha).trans (h.1 a)⟩

lemma qk_hstrip_iff {n : ℕ} (nu mu : Fin n → ℤ) (b : ℕ) : HStrip nu mu b ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip mu nu b := by
  unfold HStrip Formalism.InvariantFactorPaths.GelfandTsetlinBases.HStrip
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h m m' hm
      have := h m (by have := m'.2; omega)
      have e : (⟨m.1 + 1, by have := m'.2; omega⟩ : Fin n) = m' := Fin.ext hm
      rwa [e] at this
    · intro h a ha
      exact h a ⟨a.1 + 1, ha⟩ rfl
  · rw [sum_sub_distrib]

lemma qk_strUp_eq {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strUp mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp mu b := by
  unfold strUp Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp
  ext nu
  simp only [mem_filter, qk_hstrip_iff]

lemma qk_strDown_eq {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strDown mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown mu b := by
  unfold strDown Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown
  ext nu
  simp only [mem_filter, qk_hstrip_iff]

lemma qk_mem_strUp {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strUp mu b) : HStrip mu nu b := by
  unfold strUp at h
  simp only [mem_filter] at h
  exact h.2

lemma qk_mem_strDown {n : ℕ} {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strDown mu b) : HStrip nu mu b := by
  unfold strDown at h
  simp only [mem_filter] at h
  exact h.2

def qk_symEquiv (n b : ℕ) : SymIdx n b ≃ {P : Fin n → ℕ // ∑ i, P i = b} where
  toFun α := ⟨fun a => (α.1 a : ℕ), α.2⟩
  invFun P := ⟨fun a => ⟨P.1 a, by
    have := single_le_sum (f := P.1) (fun i _ => Nat.zero_le _) (mem_univ a)
    have h2 := P.2
    omega⟩, P.2⟩
  left_inv α := rfl
  right_inv P := rfl

lemma qk_card_symIdx (n b : ℕ) : Fintype.card (SymIdx n b) = (n + b - 1).choose b := by
  rw [Fintype.card_congr ((qk_symEquiv n b).trans (Sym.equivNatSumOfFintype (Fin n) b).symm),
    Sym.card_sym_eq_choose, Fintype.card_fin]

theorem symmetric_power_count_holds : CntSym := by
  intro n _ mu b hmu
  rw [qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).1, ← qk_strUp_eq]
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strUp hnu)).2]

theorem dual_symmetric_power_count_holds : CntSymD := by
  intro n _ mu b hmu
  rw [qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).2, ← qk_strDown_eq]
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strDown hnu)).1]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.FiltrationDirectSummand
section
noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_direct_summand_of : LemmaA → FiltrationDirectSummand := by
  intro hA n _ M CF pi hpi
  refine ⟨Submodule.span ℤ (qb_basis hA CF ℤ '' {y | CF.mu y.1 ∈ pi}ᶜ), ?_⟩
  rw [qb_Mpi_eq_image hA CF pi hpi]
  constructor
  · exact (qb_basis hA CF ℤ).linearIndependent.disjoint_span_image disjoint_compl_right
  · rw [codisjoint_iff, ← Submodule.span_union, ← Set.image_union, Set.union_compl_self, Set.image_univ]
    exact (qb_basis hA CF ℤ).span_eq

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.FiltrationGenericPointCriterion
section
noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_criterion_of : LemmaA → FiltrationGenericPointCriterion :=
  fun hA n _ M CF pi hpi F _ x => mem_span_standard_iff_proj_zero hA CF pi hpi F x

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.FiltrationMaximalQuotient
section
noncomputable section

open Finset Module

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

lemma qb_std_can (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply card_le_card
  apply filter_subset_filter
  intro b hb
  rw [qb_mem_canT] at hb ⊢
  refine lt_of_lt_of_le hb ?_
  unfold colH
  refine card_le_card fun m hm => ?_
  simp only [mem_filter, mem_univ, true_and] at hm ⊢
  omega

def standardBasis (hS : SBasis) (mu : Fin n → ℤ) (hmu : Dominant mu) : Basis {I : TIdx mu // StdT I} ℤ ↥(SMu mu) :=
  (Basis.span (hS n mu hmu).1).map (LinearEquiv.ofEq _ _ (hS n mu hmu).2)

lemma standardBasis_coe (hS : SBasis) (mu : Fin n → ℤ) (hmu : Dominant mu) (I : {I : TIdx mu // StdT I}) :
    ((standardBasis hS mu hmu I : ↥(SMu mu)) : GLCoord ℤ n) = brk mu I.1 := by
  simp [standardBasis]

def qb_bS (hS : SBasis) {nu mu : Fin n → ℤ} (hnu : Dominant nu) (h : nu = mu) :
    Basis {I : TIdx nu // StdT I} ℤ ↥(SMu mu) := h ▸ standardBasis hS nu hnu

lemma qb_bS_coe (hS : SBasis) {nu mu : Fin n → ℤ} (hnu : Dominant nu) (h : nu = mu) (I : {I : TIdx nu // StdT I}) :
    ((qb_bS hS hnu h I : ↥(SMu mu)) : GLCoord ℤ n) = brk nu I.1 := by
  subst h
  exact standardBasis_coe hS nu hnu I

def qb_canIdx {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) (j : {j : CF.J // CF.mu j = mu}) : qb_Idx CF :=
  ⟨j.1, canT _, qb_std_can _⟩

lemma qb_canIdx_inj {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) : Function.Injective (qb_canIdx CF mu) :=
  fun j j' h => Subtype.ext (congrArg Sigma.fst h)

lemma qb_can_li (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    LinearIndependent ℤ (fun j : {j : CF.J // CF.mu j = mu} => CF.vec j.1 (canT (CF.mu j.1))) := by
  have h := (qb_basisR hA CF ℤ).1
  rw [qb_vecF_int] at h
  exact h.comp (qb_canIdx CF mu) (qb_canIdx_inj CF mu)

lemma qb_can_span {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    Submodule.span ℤ (Set.range fun j : {j : CF.J // CF.mu j = mu} => CF.vec j.1 (canT (CF.mu j.1))) = CF.MM mu := by
  unfold ColFam.MM
  congr 1
  ext x
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩

def qb_bM (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    Basis {j : CF.J // CF.mu j = mu} ℤ ↥(CF.MM mu) :=
  (Basis.span (qb_can_li hA CF mu)).map (LinearEquiv.ofEq _ _ (qb_can_span CF mu))

lemma qb_bM_coe (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) (j : {j : CF.J // CF.mu j = mu}) :
    ((qb_bM hA CF mu j : ↥(CF.MM mu)) : M.ι → ℤ) = CF.vec j.1 (canT (CF.mu j.1)) := by
  simp [qb_bM]

section abs

variable {R : Type*} [CommRing R] {V A B W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup W] [Module R W] {ι κ : Type*} [DecidableEq κ] {φ : κ → Type*}

def qb_aT (bA : ∀ k, Basis (φ k) R A) (bB : Basis κ R B) : Basis (Σ k, φ k) R (TensorProduct R A B) :=
  (Finsupp.basis bA).map (TensorProduct.equivFinsuppOfBasisRight bB).symm

lemma qb_aT_apply (bA : ∀ k, Basis (φ k) R A) (bB : Basis κ R B) (x : Σ k, φ k) :
    qb_aT bA bB x = bA x.1 x.2 ⊗ₜ bB x.1 := by
  rw [qb_aT, Basis.map_apply, Finsupp.coe_basis, TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  exact Finsupp.sum_single_index (TensorProduct.zero_tmul _ _)

def qb_aPsi (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) : V →ₗ[R] W :=
  c.repr.symm.toLinearMap ∘ₗ Finsupp.lsubtypeDomain s ∘ₗ b.repr.toLinearMap

lemma qb_aPsi_basis (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) (i : ι) (hi : i ∈ s) :
    qb_aPsi b s c (b i) = c ⟨i, hi⟩ := by
  classical
  simp only [qb_aPsi, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self]
  rw [← Basis.repr_symm_single_one]
  congr 1
  ext z
  simp only [Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_apply, Finsupp.single_apply]
  congr 1
  exact propext ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

lemma qb_aPsi_eq_zero_iff (b : Basis ι R V) (s : Set ι) (c : Basis ↥s R W) (x : V) :
    qb_aPsi b s c x = 0 ↔ ∀ i ∈ s, b.repr x i = 0 := by
  simp only [qb_aPsi, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]
  rw [Finsupp.ext_iff]
  constructor
  · intro h y hy; exact h ⟨y, hy⟩
  · rintro h ⟨y, hy⟩; exact h y hy

lemma qb_quot_equiv {N T : Type*} [AddCommGroup N] [Module R N] [AddCommGroup T] [Module R T]
    (f : N →ₗ[R] T) (hs : Function.Surjective f) (p : Submodule R N) (hk : LinearMap.ker f = p) :
    ∃ Phi : (N ⧸ p) ≃ₗ[R] T, ∀ x, Phi (Submodule.Quotient.mk x) = f x := by
  subst hk
  exact ⟨f.quotKerEquivOfSurjective hs, fun x => f.quotKerEquivOfSurjective_apply_mk hs x⟩

theorem qb_aQuot (b : Basis ι R V) (s t : Set ι) (hst : s ⊆ t) (c : Basis ↥s R W) (P Q : Submodule R V)
    (hP : P = Submodule.span R (b '' t)) (hQ : Q = Submodule.span R (b '' (t \ s))) :
    ∃ Phi : (↥P ⧸ Q.comap P.subtype) ≃ₗ[R] W,
      ∀ (x : ↥P) (i : ι) (hi : i ∈ s), x.1 = b i → Phi (Submodule.Quotient.mk x) = c ⟨i, hi⟩ := by
  subst hP hQ
  have hker : LinearMap.ker (qb_aPsi b s c ∘ₗ (Submodule.span R (b '' t)).subtype) =
      (Submodule.span R (b '' (t \ s))).comap (Submodule.span R (b '' t)).subtype := by
    ext x
    have hx : ((b.repr x.1).support : Set ι) ⊆ t := (Basis.mem_span_image b).1 x.2
    rw [LinearMap.mem_ker, Submodule.mem_comap, Basis.mem_span_image]
    constructor
    · intro h y hy
      exact ⟨hx hy, fun hy' => (Finsupp.mem_support_iff.1 hy) ((qb_aPsi_eq_zero_iff b s c x.1).1 h y hy')⟩
    · intro h
      refine (qb_aPsi_eq_zero_iff b s c x.1).2 fun y hy => ?_
      by_contra hne
      exact (h (Finsupp.mem_support_iff.2 hne)).2 hy
  have hsurj : Function.Surjective (qb_aPsi b s c ∘ₗ (Submodule.span R (b '' t)).subtype) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← c.span_eq, Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    exact ⟨⟨b y, Submodule.subset_span ⟨y, hst hy, rfl⟩⟩, qb_aPsi_basis b s c y hy⟩
  obtain ⟨Phi, hPhi⟩ := qb_quot_equiv _ hsurj _ hker
  refine ⟨Phi, fun x i hi hx => ?_⟩
  rw [hPhi, LinearMap.comp_apply, Submodule.subtype_apply, hx, qb_aPsi_basis b s c i hi]

end abs

def qb_sMu {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) : Set (qb_Idx CF) := {y | CF.mu y.1 = mu}

def qb_eqS {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) :
    (Σ j : {j : CF.J // CF.mu j = mu}, {I : TIdx (CF.mu j.1) // StdT I}) ≃ ↥(qb_sMu CF mu) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

theorem filtration_maximal_quotient_of : LemmaA → SBasis → FiltrationMaximalQuotient := by
  intro hA hS n _ M CF pi hpi mu hmu hmax
  have hlow : DomLowerSet (pi \ {mu}) :=
    ⟨fun nu h => hpi.1 nu h.1, fun nu h la hla hle =>
      ⟨hpi.2 nu h.1 la hla hle, fun heq => h.2 (hmax nu h.1 (by rw [← (heq : la = mu)]; exact hle))⟩⟩
  obtain ⟨Phi, hPhi⟩ := qb_aQuot (qb_basis hA CF ℤ) (qb_sMu CF mu) {y | CF.mu y.1 ∈ pi}
    (fun y hy => by rw [Set.mem_setOf_eq, (hy : CF.mu y.1 = mu)]; exact hmu)
    ((qb_aT (fun j : {j : CF.J // CF.mu j = mu} => qb_bS hS (CF.dom j.1) j.2) (qb_bM hA CF mu)).reindex
      (qb_eqS CF mu))
    (CF.Mpi pi) (CF.Mpi (pi \ {mu})) (qb_Mpi_eq_image hA CF pi hpi) (qb_Mpi_eq_image hA CF (pi \ {mu}) hlow)
  refine ⟨Phi.toAddEquiv.toIntLinearEquiv, ?_⟩
  intro j I x y z hj hI hx hy hz
  have h1 := hPhi x ⟨j, I, hI⟩ hj (by rw [hx, qb_basis_apply, qb_vecF_int])
  rw [Basis.reindex_apply, qb_aT_apply] at h1
  refine Eq.trans h1 ?_
  congr 1
  · exact Subtype.ext ((qb_bS_coe hS _ _ _).trans hy.symm)
  · exact Subtype.ext ((qb_bM_coe hA CF mu _).trans hz.symm)

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.FiltrationStandardSpan
section
noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_standard_span_of : LemmaA → FiltrationStandardSpan :=
  fun hA n _ M CF pi hpi => qb_Mpi_eq hA CF pi hpi

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.StripDataTensorColumnFamilies
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def qx_colFam {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
    {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
    {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ} (hd : IsStripData B be Str ps)
    {M M' : GLMod n} (e : M'.ι ≃ M.ι × κ) (hT : IsTensor M M' B e) (CF : ColFam M) : ColFam M' where
  J := qx_J Str CF
  mu := fun x => (x.2 : Fin n → ℤ)
  dom := fun x => hd.2.2.1 _ (CF.dom x.1) _ x.2.2
  ph := qx_ph ps e CF
  equiv := fun x => by
    ext i I
    exact qx_equiv hd e hT CF x i I
  indepP := fun p hp nu => by
    have := Fact.mk hp
    exact qx_indep hd e CF (ZMod p) nu
  indepQ := fun nu => qx_indep hd e CF ℚ nu
  rank := qx_rank hd e CF

theorem strip_data_tensor_holds : StripDataTensorColumnFamilies := by
  intro n _ κ _ _ B be Str ps hd M M' e hT ⟨CF⟩
  exact ⟨qx_colFam hd e hT CF⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

