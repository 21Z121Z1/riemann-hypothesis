import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericPieceRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section GenericPiece

variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem isWeightedHomogeneous_map_coeff {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) {w : σ → M} {g : MvPolynomial σ R} {b : M}
    (h : IsWeightedHomogeneous w g b) : IsWeightedHomogeneous w (map f g) b := by
  intro d hd
  apply h
  intro h0
  rw [coeff_map, h0, map_zero] at hd
  exact hd rfl

theorem isWeightedHomogeneous_of_map_coeff {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) (hf : Function.Injective f) {w : σ → M}
    {g : MvPolynomial σ R} {b : M} (h : IsWeightedHomogeneous w (map f g) b) :
    IsWeightedHomogeneous w g b := by
  intro d hd
  apply h
  rw [coeff_map]
  exact (map_ne_zero_iff f hf).mpr hd

def genFibQuot (P : Ideal (MRing ι O)) :
    (MRing ι O ⧸ P) →ₐ[O] (MRing ι (FractionRing O) ⧸ genFib P) :=
  Ideal.quotientMapₐ (genFib P) (mapAlgHom (Algebra.ofId O (FractionRing O)))
    (fun _ hx => Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx))

omit [IsDomain O] [DecidableEq K] in
theorem genFibQuot_mk (P : Ideal (MRing ι O)) (g : MRing ι O) :
    genFibQuot P (Ideal.Quotient.mk P g) =
      Ideal.Quotient.mk (genFib P) (map (algebraMap O (FractionRing O)) g) := rfl

def genFibPiece (P : Ideal (MRing ι O)) (m : K → ℕ) :
    gradedPieceR P m →ₗ[O] gradedPiece (genFib P) m where
  toFun x := ⟨genFibQuot P x.1, by
    obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.mp x.2
    refine Submodule.mem_map.mpr ⟨map (algebraMap O (FractionRing O)) g, ?_, ?_⟩
    · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (isWeightedHomogeneous_map_coeff _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hg))
    · rw [← hgx]
      rfl⟩
  map_add' x y := Subtype.ext (map_add (genFibQuot P) x.1 y.1)
  map_smul' c x := Subtype.ext ((genFibQuot P).toLinearMap.map_smul c x.1)

theorem isLocalizedModule_genFibPiece (P : Ideal (MRing ι O)) (m : K → ℕ) :
    IsLocalizedModule (nonZeroDivisors O) (genFibPiece P m) where
  map_units x := by
    rw [Module.End.isUnit_iff]
    have hx : algebraMap O (FractionRing O) x ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    constructor
    · intro y z h
      have h' : algebraMap O (FractionRing O) x • y = algebraMap O (FractionRing O) x • z := by
        simpa only [Module.algebraMap_end_apply, algebraMap_smul] using h
      exact smul_right_injective _ hx h'
    · intro y
      refine ⟨(algebraMap O (FractionRing O) x)⁻¹ • y, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul (FractionRing O), smul_smul,
        mul_inv_cancel₀ hx, one_smul]
  surj y := by
    obtain ⟨q, hq⟩ := y
    obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.mp hq
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := O) (S := FractionRing O)
    obtain ⟨⟨g, c⟩, hgc⟩ :=
      IsLocalization.surj ((nonZeroDivisors O).map (C (σ := Σ k, ι k))) F
    obtain ⟨b, hb, hbc⟩ := Submonoid.mem_map.mp c.2
    simp only [algebraMap_def, ← hbc, map_C] at hgc
    have hFh : IsWeightedHomogeneous (blockWeight ι) F m :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp hF
    have hmg : IsWeightedHomogeneous (blockWeight ι) (map (algebraMap O (FractionRing O)) g) m := by
      rw [← hgc]
      intro d hd
      rw [mul_comm, coeff_C_mul] at hd
      exact hFh (right_ne_zero_of_mul hd)
    have hg : IsWeightedHomogeneous (blockWeight ι) g m :=
      isWeightedHomogeneous_of_map_coeff _ (IsFractionRing.injective O (FractionRing O)) hmg
    refine ⟨(⟨Ideal.Quotient.mk P g, Submodule.mem_map.mpr
      ⟨g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg, rfl⟩⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    change b • (Ideal.Quotient.mkₐ (FractionRing O) (genFib P)) F =
      genFibQuot P (Ideal.Quotient.mk P g)
    rw [genFibQuot_mk, ← hgc, ← algebraMap_smul (FractionRing O), ← map_smul, smul_eq_C_mul,
      mul_comm, Ideal.Quotient.mkₐ_eq_mk]
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨q₁, hq₁⟩ := x₁
    obtain ⟨q₂, hq₂⟩ := x₂
    obtain ⟨g₁, rfl⟩ := Ideal.Quotient.mk_surjective q₁
    obtain ⟨g₂, rfl⟩ := Ideal.Quotient.mk_surjective q₂
    have h₀ : genFibQuot P (Ideal.Quotient.mk P g₁) = genFibQuot P (Ideal.Quotient.mk P g₂) :=
      congrArg Subtype.val h
    rw [genFibQuot_mk, genFibQuot_mk, Ideal.Quotient.eq, ← map_sub] at h₀
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := O) (S := FractionRing O)
    rw [genFib, ← algebraMap_def,
      IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors O).map (C (σ := Σ k, ι k)))
        (MRing ι (FractionRing O))] at h₀
    obtain ⟨⟨⟨p, hp⟩, ⟨c, hc⟩⟩, hpc⟩ := h₀
    obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp hc
    simp only [algebraMap_def, ← map_mul] at hpc
    have hp' : (g₁ - g₂) * C b = p :=
      map_injective _ (IsFractionRing.injective O (FractionRing O)) hpc
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    change b • (Ideal.Quotient.mkₐ O P) g₁ = b • (Ideal.Quotient.mkₐ O P) g₂
    rw [← map_smul, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, ← smul_sub,
      smul_eq_C_mul, mul_comm, hp']
    exact hp

theorem GenericPieceRank.proof : GenericPieceRank.Statement := by
  intro O _ _ _ K _ _ ι _ P _ m
  have := isLocalizedModule_genFibPiece P m
  rw [IsFractionRing.finrank_right_eq O (FractionRing O),
    IsLocalizedModule.finrank_eq (p := nonZeroDivisors O) (f := genFibPiece P m) (hp := le_rfl)]

end GenericPiece

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGradedPieceQuot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem finite_blockWeight_eq {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  classical
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun v : (Σ k, ι k) => m v.1)).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_Iic]
  intro v
  have hcoord : (Finsupp.weight (blockWeight ι) d) v.1 =
      Finsupp.weight (fun x => blockWeight ι x v.1) d := by
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  have hle : d v ≤ Finsupp.weight (fun x => blockWeight ι x v.1) d :=
    Finsupp.le_weight _ (by simp [blockWeight]) d
  rw [← hcoord, hd] at hle
  simpa using hle

theorem finiteDimensional_weightedHomogeneousSubmodule (F : Type u) [Field F] {K : Type}
    [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_blockWeight_eq ι m).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})

theorem GradedPieceQuot.proof : GradedPieceQuot.Statement.{u} := by
  intro F _ K _ _ ι _ I m
  have := finiteDimensional_weightedHomogeneousSubmodule F ι m
  set S := weightedHomogeneousSubmodule F (blockWeight ι) m with hS
  set J : Submodule F (MRing ι F) := I.restrictScalars F with hJ
  let π : MRing ι F →ₗ[F] MRing ι F ⧸ I := (Ideal.Quotient.mkₐ F I).toLinearMap
  let q : S →ₗ[F] MRing ι F ⧸ I := π ∘ₗ S.subtype
  have hrange : LinearMap.range q = gradedPiece I m := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hkerπ : LinearMap.ker π = J := by
    ext x
    simp [π, hJ, Ideal.Quotient.eq_zero_iff_mem]
  have hker : (LinearMap.ker q).map S.subtype = S ⊓ J := by
    rw [LinearMap.ker_comp, hkerπ, Submodule.map_comap_subtype]
  have hkerdim : Module.finrank F (LinearMap.ker q) = Module.finrank F ↥(S ⊓ J) := by
    rw [← hker]
    exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype _).finrank_eq
  have hrn := LinearMap.finrank_range_add_finrank_ker q
  rw [hrange, hkerdim] at hrn
  omega

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbDegBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HilbDegBound

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_isMultiHomogIdeal {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ b, g = weightedHomogeneousComponent (blockWeight ι) b f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact hI f hf b
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, b, rfl⟩ := hx
  exact ⟨b, weightedHomogeneousComponent_isWeightedHomogeneous b f⟩

theorem isMultiHomogIdeal_sup_span {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I)
    {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  classical
  have h2 : (Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨c, (Set.mem_singleton_iff.mp hx) ▸ hs⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem
    (h := (isHomogeneous_of_isMultiHomogIdeal hI).sup h2) (hp := hf) (m := b)

theorem lt_of_add_one_le_natCast {x : WithBot ℕ∞} {N : ℕ} (h : x + 1 ≤ N) : x < N := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e, ← WithBot.coe_natCast, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top N))
    | coe a =>
      have : a + 1 ≤ N := by exact_mod_cast h
      exact_mod_cast (show a < N by omega)

theorem le_natCast_of_lt_natCast_succ {x : WithBot ℕ∞} {N : ℕ}
    (h : x < ((N + 1 : ℕ) : WithBot ℕ∞)) : x ≤ N := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_natCast, WithBot.coe_lt_coe] at h
      exact absurd h (not_lt.mpr le_top)
    | coe a =>
      have : a < N + 1 := by exact_mod_cast h
      exact_mod_cast (show a ≤ N by omega)

omit [Fintype K] [DecidableEq K] in

theorem degLT_listSum (h6 : DegLTClosure.Statement) {α : Type*} (n : ℕ)
    (g : α → (K → ℤ) → ℤ) (l : List α) (hl : ∀ a ∈ l, DegLT (g a) n) :
    DegLT (fun m => (l.map fun a => g a m).sum) n := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact degLT_zero n
  | cons a l ih =>
    have e : (fun m => ((a :: l).map fun a => g a m).sum) =
        g a + fun m => (l.map fun a => g a m).sum := by
      funext m
      simp
    rw [e]
    exact (h6 K n _ _ 0 0).1 (hl a (by simp)) (ih fun b hb => hl b (by simp [hb]))

end Lemmas

end HilbDegBound

open HilbDegBound in

theorem HilbDegBound.proof (h1 : HilbFnVanishBlock.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : PrimeFiltration.Statement.{u}) (h4 : DimStrictDrop.Statement.{u})
    (h5 : RelevantDimGe.Statement.{u}) (h6 : DegLTClosure.Statement)
    (h7 : DegLTOfUnitSteps.Statement) : HilbDegBound.Statement.{u} := by
  intro F _ K _ _ ι _ n

  have irr : ∀ (n : ℕ) (Q : Ideal (MRing ι F)), ¬ IsRelevant Q → DegLT (hilbFn Q) n := by
    intro n Q hrel
    unfold IsRelevant at hrel
    push Not at hrel
    obtain ⟨k, hk⟩ := hrel
    have hev : (0 : (K → ℤ) → ℤ) =ᶠ[Filter.atTop] hilbFn Q := by
      filter_upwards [Filter.eventually_ge_atTop (1 : K → ℤ)] with m hm
      exact (h1 F K ι Q k hk m (hm k)).symm
    exact (h6 K n 0 _ 0 0).2.2.2.2 hev (degLT_zero n)
  induction n with
  | zero =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    · exfalso
      have hge := h5 F K ι Q ⟨hQ, hQh, hrel⟩
      rw [Nat.zero_add] at hdim
      exact absurd hge (not_le.mpr hdim)
    · exact irr 0 Q hrel
  | succ n ih =>
    intro Q hQ hQh hdim
    by_cases hrel : IsRelevant Q
    swap
    · exact irr _ Q hrel
    have hdimle : ringKrullDim (MRing ι F ⧸ Q) ≤ ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      have e : n + 1 + Fintype.card K = n + Fintype.card K + 1 := by omega
      rw [e] at hdim
      exact le_natCast_of_lt_natCast_succ hdim
    apply h7 K n
    intro k
    obtain ⟨i, hi⟩ := hrel k
    have hx : IsMultiHomog (X ⟨k, i⟩ : MRing ι F) (Pi.single k 1) := isWeightedHomogeneous_X _ _ _
    have hnzd : ∀ y, (X ⟨k, i⟩ : MRing ι F) * y ∈ Q → y ∈ Q :=
      fun y hy => (hQ.mem_or_mem hy).resolve_left hi
    have hcut := h2 F K ι Q (X ⟨k, i⟩) (Pi.single k 1) hQh hx hnzd
    have hJ : IsMultiHomogIdeal (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) :=
      isMultiHomogIdeal_sup_span hQh hx
    have hs : (fun j => ((Pi.single k 1 : K → ℕ) j : ℤ)) = (Pi.single k 1 : K → ℤ) := by
      funext j
      by_cases h : j = k <;> simp [h]
    have heq : diffStep (Pi.single k 1) (hilbFn Q) =
        hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) := by
      funext m
      rw [hcut m, hs]
      rfl
    rw [heq]
    obtain ⟨l, hl1, hl2, -⟩ := h3 F K ι _ hJ
    obtain ⟨G, hG⟩ : ∃ G : Ideal (MRing ι F) × (K → ℕ) → (K → ℤ) → ℤ,
        G = fun p => shiftFn (fun j => (p.2 j : ℤ)) (hilbFn p.1) := ⟨_, rfl⟩
    have hfun : hilbFn (Q ⊔ Ideal.span {(X ⟨k, i⟩ : MRing ι F)}) = fun m =>
        (l.map fun p => G p m).sum := by
      funext m
      rw [hl2 m, hG]
      rfl
    rw [hfun]
    apply degLT_listSum h6 n G l
    intro p hp
    obtain ⟨hp1, hp2, hp3⟩ := hl1 p hp
    rw [hG]
    refine (h6 K n (hilbFn p.1) 0 0 _).2.2.1 ?_
    refine ih p.1 hp1 hp2 ?_
    have hlt : Q < p.1 := by
      refine lt_of_le_of_ne (le_sup_left.trans hp3) fun h => hi ?_
      rw [h]
      exact hp3 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have := hQ
    have := hp1
    have hd := h4 (MRing ι F) Q p.1 hlt
    exact lt_of_add_one_le_natCast (hd.trans hdimle)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem HilbFnCut.proof (h1 : GradedPieceQuot.Statement.{u}) (h2 : CutPieces.Statement.{u}) :
    HilbFnCut.Statement.{u} := by
  intro F _ K _ _ ι _ I x e hI hx hnzd m
  by_cases hm : ∀ k, 0 ≤ m k
  · set n : K → ℕ := fun k => (m k).toNat with hn
    have hA := h1 F K ι (I ⊔ Ideal.span {x}) n
    have hB := h1 F K ι I n
    have hC := h2 F K ι I x e n hI hx hnzd
    have hL : hilbFn (I ⊔ Ideal.span {x}) m =
        (Module.finrank F (gradedPiece (I ⊔ Ideal.span {x}) n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    have hM : hilbFn I m = (Module.finrank F (gradedPiece I n) : ℤ) := by
      unfold hilbFn; rw [if_pos hm]
    rw [hL, hM, hA, hB]
    by_cases he : e ≤ n
    · have hme : ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hq : (fun k => ((m - fun k => (e k : ℤ)) k).toNat) = n - e := by
        funext k
        have h1k := he k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) =
          (Module.finrank F (gradedPiece I (n - e)) : ℤ) := by
        unfold hilbFn; rw [if_pos hme, hq]
      rw [hN, h1 F K ι I (n - e)]
      rw [if_pos he] at hC
      rw [hC]
      ring
    · have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
        intro hall
        apply he
        intro k
        have h1k := hall k
        have h0 := hm k
        simp only [Pi.sub_apply, hn] at h1k ⊢
        omega
      have hN : hilbFn I (m - fun k => (e k : ℤ)) = 0 := by
        unfold hilbFn; rw [if_neg hme]
      rw [hN]
      rw [if_neg he] at hC
      rw [hC]
      ring
  · obtain ⟨k, hk⟩ := not_forall.mp hm
    have hme : ¬ ∀ k, 0 ≤ (m - fun k => (e k : ℤ)) k := by
      intro hall
      have := hall k
      simp only [Pi.sub_apply] at this
      omega
    unfold hilbFn
    rw [if_neg hm, if_neg hm, if_neg hme, sub_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHilbFnVanishBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem exists_block_var_of_weight_pos {K : Type} [DecidableEq K] {ι : K → Type}
    (d : (Σ k, ι k) →₀ ℕ) (k : K) (h : 1 ≤ Finsupp.weight (blockWeight ι) d k) :
    ∃ v : Σ k, ι k, v.1 = k ∧ d v ≠ 0 := by
  by_contra hne
  push Not at hne
  have h0 : Finsupp.weight (blockWeight ι) d k = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun v hv => ?_
    have hv1 : v.1 ≠ k := fun e => (Finsupp.mem_support_iff.mp hv) (hne v e)
    simp [blockWeight, hv1]
  omega

theorem mem_of_block_vars_mem {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
    (Q : Ideal (MRing ι F)) (k : K) (hX : ∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ Q) (m : K → ℕ)
    (hm : 1 ≤ m k) (f : MRing ι F) (hf : f ∈ weightedHomogeneousSubmodule F (blockWeight ι) m) :
    f ∈ Q := by
  have hspan : Ideal.span ((X : (Σ k, ι k) → MRing ι F) '' {v | v.1 = k}) ≤ Q := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨k', i⟩, hv, rfl⟩
    simp only [Set.mem_ofPred_eq] at hv
    subst hv
    exact hX i
  apply hspan
  rw [mem_ideal_span_X_image]
  intro d hd
  rw [mem_weightedHomogeneousSubmodule] at hf
  have hw : Finsupp.weight (blockWeight ι) d = m := hf (Finsupp.mem_support_iff.mp hd)
  obtain ⟨v, hv, hdv⟩ := exists_block_var_of_weight_pos d k (by rw [hw]; exact hm)
  exact ⟨v, hv, hdv⟩

theorem HilbFnVanishBlock.proof : HilbFnVanishBlock.Statement.{u} := by
  intro F _ K _ _ ι _ Q k hX m hm
  unfold hilbFn
  split_ifs with h
  · have hbot : gradedPiece Q (fun k => (m k).toNat) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
      have hfQ : f ∈ Q := mem_of_block_vars_mem Q k hX _ (by omega) f hf
      simpa using (Ideal.Quotient.eq_zero_iff_mem).mpr hfQ
    rw [hbot, finrank_bot]
    rfl
  · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
end

