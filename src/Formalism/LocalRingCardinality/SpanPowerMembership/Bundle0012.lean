import Formalism.LocalRingCardinality.SpanPowerMembership.RangeInclEqSpan
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.Bundle0002
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0003
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0011

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.EmbeddingBaseFieldCondition
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

section Coord

variable {K F W ι : Type} [Field K] [Field F] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι]
  (σ : K →+* F) (b : Module.Basis ι K W)

def coordMap : W →ₛₗ[σ] (ι → F) where
  toFun x a := σ (b.repr x a)
  map_add' x y := funext fun a => by simp
  map_smul' c x := funext fun a => by simp

theorem coordMap_apply (x : W) (a : ι) : coordMap σ b x a = σ (b.repr x a) := rfl

theorem coordMap_basis (i : ι) : coordMap σ b (b i) = Pi.single i 1 := by
  funext a
  rw [coordMap_apply, b.repr_self, Finsupp.single_apply, Pi.single_apply]
  split_ifs with h1 h2 h2
  · exact map_one σ
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero σ

theorem coordMap_good : LinearIndependent F (fun i => coordMap σ b (b i)) ∧
    Submodule.span F (Set.range fun i => coordMap σ b (b i)) = ⊤ := by
  have e : (fun i => coordMap σ b (b i)) = ⇑(Pi.basisFun F ι) :=
    funext fun i => (coordMap_basis σ b i).trans (Pi.basisFun_apply _ _ i).symm
  rw [e]
  exact ⟨(Pi.basisFun F ι).linearIndependent, (Pi.basisFun F ι).span_eq⟩

theorem coordMap_image_range : coordMap σ b '' Set.range b = Set.range fun a : ι => (Pi.single a 1 : ι → F) := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun i => coordMap_basis σ b i)

end Coord

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)

def gapN : TwGap D where
  ntw := C.toTwN I
  nexp := C.toExpN I
  nth := C.toThN I
  ntwbr := C.br
  ntwbr_ind := C.br_ind
  nStage_trivialCharacter_coeff_eq := he
  cover := C.cover

abbrev recN : D7 := withTw D (gapN D C I he)

set_option synthInstance.maxHeartbeats 400000 in

structure EmbC where
  twI : D.what₂.places.Pl → C.Tw
  twI_l : ∀ w, C.l (twI w) = D.what₂.places.resChar w
  embW : ∀ w, D.what₂.LL →+* FractionRing (C.Ok (twI w) 1)
  embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    embW w x ∈ (algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))).range
  embedding_baseField_condition : ∀ w (x : D.LL0) (y z : C.O0 (twI w)), z ≠ 0 →
    C.emb0 (twI w) x * algebraMap (C.O0 (twI w)) (FractionRing (C.O0 (twI w))) z =
      algebraMap (C.O0 (twI w)) (FractionRing (C.O0 (twI w))) y →
    embW w (x : D.what₂.LL) * algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))
        (algebraMap (C.O (twI w)) (C.Ok (twI w) 1) (algebraMap (C.O0 (twI w)) (C.O (twI w)) z)) =
      algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))
        (algebraMap (C.O (twI w)) (C.Ok (twI w) 1) (algebraMap (C.O0 (twI w)) (C.O (twI w)) y))

variable (E : EmbC D C)

structure StdMt where
  bT : ∀ w j, Module.Basis (I.ixM j) D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  bT_gen : ∀ w j, {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen} = Set.range (bT w j)

variable (S : StdMt D C I)

def eMtN (w : D.what₂.places.Pl) (j : ℕ) :
    D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[E.embW w] (I.ixM j → FractionRing (C.Ok (E.twI w) 1)) :=
  coordMap (E.embW w) (S.bT w j)

theorem eMtN_basis (w : D.what₂.places.Pl) (j : ℕ)
    (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) :
    LinearIndependent (FractionRing (C.Ok (E.twI w) 1)) (fun i => eMtN D C I E S w j (b i)) ∧
      Submodule.span (FractionRing (C.Ok (E.twI w) 1)) (Set.range fun i => eMtN D C I E S w j (b i)) = ⊤ :=
  haveI : Module.Finite D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := Module.Finite.of_basis (S.bT w j)
  haveI : Finite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) :=
    Module.Finite.finite_basis b
  letI : Fintype (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := Fintype.ofFinite _
  basis_of_basisF (E.embW w) (coordMap (E.embW w) (S.bT w j)) (S.bT w j)
    (coordMap_good (E.embW w) (S.bT w j)) b

theorem eMtN_lat (w : D.what₂.places.Pl) (j : ℕ) :
    Submodule.span (C.Ok (E.twI w) 1)
      (eMtN D C I E S w j '' {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}) =
    LinearMap.range (TwCore.incl (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) (I.ixM j)) := by
  rw [S.bT_gen w j, TwCore.range_incl_eq_span]
  exact congrArg _ (coordMap_image_range (E.embW w) (S.bT w j))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def nchN : NChoice (recN D C I he) :=
  NChoice.ofOk (recN D C I he) E.twI E.twI_l (fun _ => true) (fun _ => ∅) (fun _ => 1) (fun _ => 1) E.embW E.embW_w
    (eMtN D C I E S) (fun w j _ _ _ => eMtN_basis D C I E S w j) (fun w j _ _ _ => eMtN_lat D C I E S w j)

set_option synthInstance.maxHeartbeats 400000 in

theorem nchN_tie : NChTie (recN D C I he) (nchN D C I he E S) where
  twOf_eq := fun a => hL.elim a
  twSide_eq := fun a => hL.elim a
  Q_eq := fun a => hL.elim a
  psi_eq := ⟨fun _ => 1, fun _ => rfl, fun w _ => (map_one (E.embW w)).trans
    (map_one (algebraMap (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)))).symm, fun a => hL.elim a⟩
  embedding_baseField_condition := E.embedding_baseField_condition

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZColE
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical Module

section Desc

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]
  (σ : K →+* Kf) (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))

include hσ in

theorem desc {V W ι : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (b : Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (B : Submodule A V) (x : V)
    (hx : φ x ∈ Submodule.span O (φ '' (B : Set V))) : ∃ s : A, s ∉ w.asIdeal ∧ s • x ∈ B := by
  have h1 : (1 : A) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  by_cases hx0 : x = 0
  · exact ⟨1, h1, by rw [hx0, smul_zero]; exact B.zero_mem⟩
  have hφx : φ x ≠ 0 :=
    (FBC.li_of_basis_li σ φ hφ b hb (fun _ : Unit => x) (LinearIndependent.of_subsingleton () hx0)).ne_zero ()
  have h2 := (FBC.flat_ext w σ hσ φ hφ b hb).2 B (Submodule.span K {x})
  have h3 : φ x ∈ Submodule.span O (φ '' ((B ⊓ (Submodule.span K {x}).restrictScalars A : Submodule A V) : Set V)) := by
    rw [← h2]
    exact ⟨hx, Submodule.subset_span ⟨x, Submodule.mem_span_singleton_self x, rfl⟩⟩
  by_contra hno
  have hlt : ∀ k : K, k • x ∈ B → w.valuation K k < 1 := by
    intro k hk
    by_contra hge
    rw [not_lt] at hge
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hge
    obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer k⁻¹ (by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hge)
    refine hno ⟨d, d.2, ?_⟩
    have : (d : A) • x = n • (k • x) := by
      rw [← algebraMap_smul K (d : A), ← algebraMap_smul K n, smul_smul, ← hnd, mul_assoc, mul_comm _ k, ← mul_assoc,
        inv_mul_cancel₀ hk0, one_mul]
    rw [this]
    exact B.smul_mem _ hk
  have h4 : Submodule.span O (φ '' ((B ⊓ (Submodule.span K {x}).restrictScalars A : Submodule A V) : Set V)) ≤
      IsLocalRing.maximalIdeal O • Submodule.span O {φ x} := by
    rw [Submodule.span_le]
    rintro _ ⟨y, ⟨hyB, hyU⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hyU
    have hk := hlt k hyB
    obtain ⟨o, ho⟩ := (hσ k).1 hk.le
    refine Submodule.mem_smul_span_singleton.mpr ⟨o, ?_, ?_⟩
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨o', ho'⟩ := hu.exists_right_inv
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [map_zero] at ho
        have : o = 0 := IsFractionRing.injective O Kf (by rw [ho, map_zero])
        rw [this, zero_mul] at ho'
        exact zero_ne_one ho'
      have h5 : σ k⁻¹ = algebraMap O Kf o' := by
        have := congrArg (algebraMap O Kf) ho'
        rw [map_mul, map_one, ho] at this
        rw [map_inv₀]
        exact inv_eq_of_mul_eq_one_right this
      have h6 := (hσ k⁻¹).2 ⟨o', h5.symm⟩
      rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff (w.valuation K)).mpr hk0)] at h6
      exact absurd hk (not_lt.mpr h6)
    · rw [hφ, ← ho, algebraMap_smul]
  obtain ⟨m, hm, hmx⟩ := Submodule.mem_smul_span_singleton.mp (h4 h3)
  have hu : IsUnit (1 - m) := by
    by_contra hnu
    have : (1 - m) + m ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.maximalIdeal O).add_mem ((IsLocalRing.mem_maximalIdeal _).mpr hnu) hm
    rw [sub_add_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  have h7 : (1 - m) • φ x = 0 := by rw [sub_smul, one_smul, hmx, sub_self]
  exact hφx ((hu.smul_eq_zero).mp h7)

end Desc

end Formalism.BasicNotions.Examples₂.NZ
end
end

