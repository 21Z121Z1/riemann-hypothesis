import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVecOfNe
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.KapRedII

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def StepLevAt (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) : Prop :=
  ∀ (k : ℕ), k + 1 < D.R.m → ∀ y : R.CC t (k + 1),
    y.1 ∈ MultT R.θ (R.MY (k + 1)) (levS _ (R.βY (k + 1)) (R.datYt t (k + 1) (R.levR F b)))
        (levChi _ (R.βY (k + 1)) (R.datYt t (k + 1) (R.levR F b))) →
      (R.ioY t k y).1 ∈ MultT R.θ (R.MY k) (levS _ (R.βY k) (R.datYt t k (R.levR F b)))
        (levChi _ (R.βY k) (R.datYt t k (R.levR F b)))

def TopLevAt (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) : Prop :=
  ∀ (y : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)),
    y.1 ∈ MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) →
      (R.ioX t y).1 ∈ MultT R.θ (R.MY (D.R.m - 1)) (levS _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) (R.levR F b)))
        (levChi _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) (R.levR F b)))

def RowProjAt (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) : Prop :=
  ∀ (w : MMap (R.MY 0)),
    w ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.datYt t 0 (R.levR F b))) (levChi _ (R.βY 0) (R.datYt t 0 (R.levR F b))) →
      postOn (R.MY 0) R.e0 w ∈ goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b)))
          (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0 ∧
        ∀ c ∈ goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) R.e0,
          ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F b)⁻¹ • R.ν0) R.fd0 c w =
            ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F b)⁻¹ • R.ν0) R.fd0 c (postOn (R.MY 0) R.e0 w)

def TopAdjAt (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) : Prop :=
  ∀ y : R.HE.H, R.HE.e y ∈ R.EEat (R.levR F b) →
    R.cX.toMap R.prX ((R.HX t).e (LinearMap.adjoint (R.Th t) y)) ∈
      MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b)))

theorem nP_pos' (F : Face D A) (b : Bool) : 0 < RealDat.nP F b := by
  have hcard : 0 < Nat.card (F.lvl b).P := Nat.card_pos
  unfold RealDat.nP
  exact_mod_cast hcard

end Defs

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ} {a : ℝ}
    (ha : 0 ≤ a) (h : IsMultIP M μ 𝓕 T T' c) : IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' ((a : ℂ) * c) := by
  intro v v'
  obtain ⟨hint, heq⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn
    rw [Measure.restrict_smul]
    exact hint.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, heq, ENNReal.toReal_ofReal ha, Complex.real_smul]
    ring

private theorem isMultIP_const_unique {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c c' : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0)
    (h : IsMultIP M μ 𝓕 T T' c) (h' : IsMultIP M μ 𝓕 T T' c') : c = c' := by
  have e := (h v v).2
  rw [(h' v v).2] at e
  exact (mul_right_cancel₀ hv e).symm

private theorem ipM_eq_of_isMultIP {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {T T' : MMap M} {c : ℂ}
    (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) (h : IsMultIP M μ 𝓕 T T' c) :
    ipM M μ 𝓕 T T' = c := by
  have hex : ∃ c, IsMultIP M μ 𝓕 T T' c := ⟨c, h⟩
  unfold ipM
  rw [dif_pos hex]
  exact isMultIP_const_unique v hv hex.choose_spec h

theorem ipM_smul_of_vec (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {a : ℝ}
    (ha : 0 < a) (v : M.Vec) (hv : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 T T' = (a : ℂ) * ipM M μ 𝓕 T T' := by
  by_cases hex : ∃ c, IsMultIP M μ 𝓕 T T' c
  · obtain ⟨c, hc⟩ := hex
    rw [ipM_eq_of_isMultIP v hv hc, ipM_eq_of_isMultIP v hv (isMultiplicityInner_smul_measure ha.le hc)]
  ·
    have hex' : ¬ ∃ c, IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' c := by
      rintro ⟨c', hc'⟩
      have hb := isMultiplicityInner_smul_measure (inv_nonneg.mpr ha.le) hc'
      rw [smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one,
        one_smul] at hb
      exact hex ⟨_, hb⟩
    unfold ipM
    rw [dif_neg hex, dif_neg hex', mul_zero]

theorem exists_vec_of_ne {M : DSModel V S} {T : MMap M} (hT : T ≠ 0) :
    ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  classical

  obtain ⟨v, hv⟩ : ∃ v : M.Vec, T v ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hT (MultilinearMap.ext fun x => by simp [hno x])
  refine ⟨v, Finset.prod_ne_zero_iff.mpr fun τ _ => ?_⟩
  have hvt : v τ ≠ 0 := fun h0 => hv (T.map_coord_zero τ h0)
  rw [inner_self_ne_zero, ne_eq, Submodule.coe_eq_zero]
  exact hvt

end Schur

end GlobalTheory.KapRedII
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagAction

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem conj_mem_flag1 {g0 : G0 L.Pg L.r} {κ k : GA D V} (hκ : IsLevelLift V β L g0 κ)
    (hk : k ∈ levG V β (flag1L L)) :
    κ⁻¹ * (k * κ) ∈ levG V β (flag1L L) ∧
      levChi V β (flag1L L) (κ⁻¹ * (k * κ)) = levChi V β (flag1L L) k := by
  obtain ⟨hκf, hκp, hκr⟩ := hκ
  rw [levG, mem_levA, Formalism.L2.DIV.mem_lev] at hk
  obtain ⟨hkf, hkp, hkr⟩ := hk

  have hxp : finE V k ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := hkp
  have hx1 : Formalism.L2.DIV.rTup β L (finE V k) = 1 := Subgroup.mem_bot.mp hkr
  have hfin : finE V (κ⁻¹ * (k * κ)) = (finE V κ)⁻¹ * (finE V k * finE V κ) := by
    rw [map_mul, map_mul, map_inv]
  have hcp : (finE V κ)⁻¹ * (finE V k * finE V κ) ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hκp) (Subgroup.mul_mem _ hxp hκp)
  refine ⟨?_, ?_⟩
  · rw [levG, mem_levA, Formalism.L2.DIV.mem_lev, hfin]
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hκf) (Subgroup.mul_mem _ hkf hκf), hcp, ?_⟩
    have hr : Formalism.L2.DIV.rTup β L ((finE V κ)⁻¹ * (finE V k * finE V κ)) = 1 := by
      rw [Formalism.L2.DIV.rTup_mul (Subgroup.inv_mem _ hκp) (Subgroup.mul_mem _ hxp hκp),
        Formalism.L2.DIV.rTup_inv hκp, Formalism.L2.DIV.rTup_mul hxp hκp, hx1, one_mul, inv_mul_cancel]
    exact Subgroup.mem_bot.mpr hr
  ·
    show ((Formalism.L2.DIV.levFn β (flag1L L) (finE V (κ⁻¹ * (k * κ))) : ℂˣ) : ℂ) =
      ((Formalism.L2.DIV.levFn β (flag1L L) (finE V k) : ℂˣ) : ℂ)
    rw [levFn_flag1, levFn_flag1, hfin]
    have hA : finE V κ ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) :=
      Formalism.L2.DIV.mem_lev.mpr ⟨hκp, Subgroup.mem_top _⟩
    have hX : finE V k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) :=
      Formalism.L2.DIV.mem_lev.mpr ⟨hxp, Subgroup.mem_top _⟩
    let A : Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := ⟨finE V κ, hA⟩
    let X : Formalism.L2.DIV.lev D.sp.cm V.gram β (flagL L) := ⟨finE V k, hX⟩
    have hc : Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L) (A⁻¹ * (X * A)) =
        Formalism.L2.DIV.levChar D.sp.cm V.gram β (flagL L) X := by
      rw [map_mul, map_mul, map_inv]
      exact inv_mul_cancel_comm_assoc _ _
    have e1 := Formalism.L2.DIV.levChar_apply (A⁻¹ * (X * A))
    have e2 := Formalism.L2.DIV.levChar_apply X
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (e1.symm.trans (hc.trans e2))

theorem finiteGroupAction_preserves_principalFlagMultiplicity : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), IsInfFam θ → ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r), ∀ T ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)), ∀ U : MMap M, (∀ v, U v = actG0 V β L g0 (T v)) → U ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  intro D V S θ M _ β L g0 T hT U hU
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  ·
    have hκ : IsLevelLift V β L g0 hk.choose := hk.choose_spec
    have hEq : U = (levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T := by
      ext v h
      rw [hU v, MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      unfold actG0
      rw [dif_pos hk]
      congr 1
      show T v (h * hk.choose) = ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (h * γ)
      rw [Finset.sum_singleton]
    rw [hEq]
    refine GlobalTheory.MultMem.isMultMap_smul _ (GlobalTheory.SphericalOps.isMultMap_heckeOn hT ?_ ?_)
    · intro k hk'
      rw [Finset.mem_singleton.mp hk']
      exact hκ.1
    · intro v k hkJ g
      show ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (g * k * γ) =
        levChi V β (flag1L L) k * ∑ γ ∈ ({hk.choose} : Finset (GA D V)), T v (g * γ)
      rw [Finset.sum_singleton, Finset.sum_singleton]
      obtain ⟨hmem, hchi⟩ := conj_mem_flag1 hκ hkJ
      have hl := hT.lev v _ hmem (g * hk.choose)
      rw [hchi] at hl
      rw [← hl]
      congr 1
      simp [mul_assoc]
  ·
    have hEq : U = 0 := by
      ext v h
      rw [hU v]
      unfold actG0
      rw [dif_neg hk]
      rfl
    rw [hEq]
    exact GlobalTheory.MultMem.isMultMap_zero

end GlobalTheory.FlagAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePreimageOfNhdsZero
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix Topology

noncomputable section

namespace GlobalTheory.TrFinite

theorem finite_preimage_of_nhds_zero {A G : Type} [AddCommGroup A] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (f : A →+ G) {U : Set G} (hU : U ∈ 𝓝 (0 : G)) (h : ∀ x, f x ∈ U → x = 0)
    {K : Set G} (hK : IsCompact K) : {x | f x ∈ K}.Finite := by
  obtain ⟨V, hV0, hV⟩ : ∃ V ∈ 𝓝 (0 : G), ∀ a ∈ V, ∀ b ∈ V, a - b ∈ U := by
    have ht : Tendsto (fun p : G × G => p.1 - p.2) (𝓝 ((0 : G), (0 : G))) (𝓝 0) := by
      simpa using (continuous_sub.tendsto ((0 : G), (0 : G)))
    have h2 := ht hU
    rw [nhds_prod_eq] at h2
    obtain ⟨V1, h1, V2, h2', hs⟩ := Filter.mem_prod_iff.1 h2
    exact ⟨V1 ∩ V2, inter_mem h1 h2', fun a ha b hb => @hs (a, b) ⟨ha.1, hb.2⟩⟩
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => (fun y => y - k) ⁻¹' V) (fun k _ => by
    have hc : Continuous fun y : G => y - k := continuous_id.sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV0))
  have hsub : {x | f x ∈ K} ⊆ ⋃ k ∈ t, {x | f x - k ∈ V} := fun x hx => by
    have := ht hx
    simp only [Set.mem_iUnion, Set.mem_preimage] at this ⊢
    exact this
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun k _ => ?_) hsub
  refine Set.Subsingleton.finite fun x hx y hy => ?_
  have hm : f (x - y) ∈ U := by
    have := hV _ hx _ hy
    rwa [sub_sub_sub_cancel_right, ← map_sub] at this
  exact sub_eq_zero.1 (h _ hm)

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end GlobalTheory.TrFinite

namespace GlobalTheory.TrFinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem charpoly_conj_ratEmb (γ : GRat σ J) (x : GAd σ J) :
    (((matHom (AF F) σ J (x⁻¹ * ratEmb σ J γ * x) : GL (Fin n) (AF F ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly = γ.1.1.charpoly.map (inclR (AF F)) := by
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']
  exact Matrix.charpoly_map _ _

theorem finite_ratEmb_mem {K : Set (GAd σ J)} (hK : IsCompact K) : {γ : GRat σ J | ratEmb σ J γ ∈ K}.Finite := by
  haveI : DiscreteTopology (ratPts σ J) := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have hcl : IsClosed (ratPts σ J : Set (GAd σ J)) := Subgroup.isClosed_of_discrete
  have hfin : ((Subtype.val : ratPts σ J → GAd σ J) ⁻¹' K).Finite :=
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  let g : GRat σ J → ratPts σ J := fun γ => ⟨ratEmb σ J γ, range_ratEmb σ J ▸ ⟨γ, rfl⟩⟩
  have hg : Function.Injective g := fun a b h => ratEmb_injective σ J (congrArg Subtype.val h)
  exact Set.Finite.preimage (f := g) hg.injOn hfin

theorem finite_charpoly_and_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J)), IsCompact C →
    {Q : E[X] | ∃ γ : GRat σ J, γ.1.1.charpoly = Q ∧ ∃ x, x⁻¹ * ratEmb σ J γ * x ∈ C}.Finite ∧
      ∀ x, {γ : GRat σ J | x⁻¹ * ratEmb σ J γ * x ∈ C}.Finite := by
  intro F E _ _ _ _ _ σ _ n J C hC
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  refine ⟨?_, fun x => ?_⟩
  ·
    let c : Fin (n + 1) → GAd σ J → AF F ⊗[F] E := fun i g =>
      (((matHom (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly.coeff i
    have hc : ∀ i, Continuous (c i) := fun i =>
      (continuous_coeff_charpoly n i).comp (Units.continuous_val.comp continuous_subtype_val)
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
    let T : Fin (n + 1) → Set E := fun i => {e | (inclR (AF F)).toAddMonoidHom e ∈ c i '' C}
    have hT : ∀ i, (T i).Finite := fun i =>
      finite_preimage_of_nhds_zero _ hU hU0 (hC.image (hc i))
    let S := {Q : E[X] | ∃ γ : GRat σ J, γ.1.1.charpoly = Q ∧ ∃ x, x⁻¹ * ratEmb σ J γ * x ∈ C}
    let φ : E[X] → Fin (n + 1) → E := fun Q i => Q.coeff i
    have hdeg : ∀ Q ∈ S, Q.natDegree = n := by
      rintro Q ⟨γ, rfl, -⟩
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hinj : Set.InjOn φ S := fun P hP Q hQ h => by
      ext i
      by_cases hi : i ≤ n
      · exact congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
      · push_neg at hi
        rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg P hP]; exact hi),
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg Q hQ]; exact hi)]
    have himg : φ '' S ⊆ Set.pi Set.univ T := by
      rintro _ ⟨Q, ⟨γ, rfl, x, hx⟩, rfl⟩ i -
      refine ⟨_, hx, ?_⟩
      change (((matHom (AF F) σ J (x⁻¹ * ratEmb σ J γ * x) : GL (Fin n) (AF F ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).charpoly.coeff i = inclR (AF F) (γ.1.1.charpoly.coeff i)
      rw [charpoly_conj_ratEmb, coeff_map]
    exact Set.Finite.of_finite_image ((Set.Finite.pi hT).subset himg) hinj
  · have hK : IsCompact ((fun g => x * g * x⁻¹) '' C) :=
      hC.image ((continuous_const.mul continuous_id).mul continuous_const)
    refine (finite_ratEmb_mem σ J hK).subset fun γ hγ => ⟨_, hγ, ?_⟩
    change x * (x⁻¹ * ratEmb σ J γ * x) * x⁻¹ = ratEmb σ J γ
    group

end GlobalTheory.TrFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsumRestrictedFamilyEqProdFinsum
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem finsum_restrictedFamily_eq_prod_finsum : ∀ (V W : Type) [Fintype W] (C : V → Type) [∀ v, One (C v)] (X : ∀ v, Set (C v)) (Y : W → Type) [∀ w, Finite (Y w)], (∀ v, (X v).Finite) → ∀ (o : ∀ v, X v → ℂ) (oa : ∀ w, Y w → ℂ), (∀ᶠ v in cofinite, (1 : C v) ∈ X v ∧ ∀ q : X v, (q.1 = 1 → o v q = 1) ∧ (q.1 ≠ 1 → o v q = 0)) → (Function.support fun p : {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1} => (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w)).Finite ∧ ∑ᶠ p : {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1}, (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w) = (∏ᶠ v, ∑ᶠ q : X v, o v q) * ∏ w, ∑ᶠ q : Y w, oa w q := by
  intro V W _ C _ X Y _ hX o oa hev
  classical
  have hfin := Filter.eventually_cofinite.1 hev
  set S : Finset V := hfin.toFinset with hSdef
  have hS : ∀ v, v ∉ S → ((1 : C v) ∈ X v ∧ ∀ q : X v, (q.1 = 1 → o v q = 1) ∧ (q.1 ≠ 1 → o v q = 0)) := by
    intro v hv
    by_contra h
    exact hv (by simpa [hSdef] using h)
  haveI : ∀ v, Fintype (X v) := fun v => (hX v).fintype
  haveI : ∀ w, Fintype (Y w) := fun w => Fintype.ofFinite _
  let Sub := {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1}
  let F : Sub → ℂ := fun p => (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w)
  let emb : (∀ v : S, X v) × (∀ w, Y w) → Sub := fun t =>
    ⟨(fun v => if h : v ∈ S then t.1 ⟨v, h⟩ else ⟨1, (hS v h).1⟩, t.2), by
      refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
      by_contra h
      simp [dif_neg (show v ∉ S from h)] at hv⟩
  have hmul : ∀ p : Sub, (Function.mulSupport fun v => o v (p.1.1 v)).Finite := by
    intro p
    refine (S.finite_toSet.union (Filter.eventually_cofinite.1 p.2)).subset ?_
    intro v hv
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (((hS v h.1).2 _).1 h.2)
  have hsupp : Function.support F ⊆ Set.range emb := by
    intro p hp
    have h1 : ∀ v, v ∉ S → (p.1.1 v).1 = 1 := by
      intro v hv
      by_contra hne
      apply hp
      show (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w) = 0
      rw [finprod_eq_zero _ v (((hS v hv).2 _).2 hne) (hmul p), zero_mul]
    refine ⟨(fun v => p.1.1 v, p.1.2), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · funext v
      by_cases hv : v ∈ S
      · simp only [emb, dif_pos hv]
      · simp only [emb, dif_neg hv]
        exact Subtype.ext (h1 v hv).symm
    · rfl
  have hinj : Function.Injective emb := by
    intro t t' h
    have h' := congrArg (fun p : Sub => p.1) h
    simp only [emb, Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    refine Prod.ext (funext fun v => ?_) h2
    have := congrFun h1 v.1
    simpa only [dif_pos v.2] using this
  have hval : ∀ t, F (emb t) = (∏ v : S, o v (t.1 v)) * ∏ w, oa w (t.2 w) := by
    intro t
    show (∏ᶠ v, o v ((emb t).1.1 v)) * ∏ w, oa w (t.2 w) = _
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [emb, dif_pos v.2]
    · intro v hv
      by_contra h
      apply hv
      simp only [emb, dif_neg (show v ∉ S from h)]
      exact ((hS v h).2 _).1 rfl
  have hsupp' : Function.support F ⊆ ↑(Finset.univ.image emb) := by
    intro p hp
    obtain ⟨t, rfl⟩ := hsupp hp
    simp
  refine ⟨(Finset.univ.image emb).finite_toSet.subset hsupp', ?_⟩
  show ∑ᶠ p, F p = _
  rw [finsum_eq_sum_of_support_subset _ hsupp', Finset.sum_image (fun a _ b _ h => hinj h)]
  simp only [hval]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Fintype.sum_mul_sum, ← Fintype.prod_sum, ← Fintype.prod_sum]
  congr 1
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [finsum_eq_sum_of_fintype]
    · intro v hv
      by_contra h
      apply hv
      show ∑ᶠ q : X v, o v q = 1
      rw [finsum_eq_single _ ⟨1, (hS v h).1⟩]
      · exact ((hS v h).2 _).1 rfl
      · intro q hq
        exact ((hS v h).2 q).2 (fun e => hq (Subtype.ext e))
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [finsum_eq_sum_of_fintype]

end GlobalTheory.TrEll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointActionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrixAdjoint_jointAction : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D T) (x : WO S T), frMapAdj S T βS βT (actO S T 1 g x) = HMul.hMul (frMapAdj S T βS βT x) ((βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT)⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  first | exact @GlobalTheory.AdjAct.frMapAdj_actO | exact GlobalTheory.AdjAct.frMapAdj_actO | (intros; apply GlobalTheory.AdjAct.frMapAdj_actO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointSupportedOfConjHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrixAdjoint_supported_of_conjHalf : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T), e * e = e → IsHalf (cA D e) x → ∀ i j, toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  first | exact @GlobalTheory.HalfSupp.frMapAdj_supp | exact GlobalTheory.HalfSupp.frMapAdj_supp | (intros; apply GlobalTheory.HalfSupp.frMapAdj_supp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GUnitOfModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem gUnit_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.IsModels → R.PGUnit F := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hM
  have hE := GlobalTheory.norm_gE_rows R.toRealDat hM.HE hM.gE hM.ν0
  have hW := GlobalTheory.gW_norm_eq R.toRealDat hM.HW hM.gW hM.νW
  refine ⟨fun g x y => ?_, fun j g x y => ?_⟩
  ·     exact congrArg _ (LinearIsometry.inner_map_map (⟨R.gE g, hE g⟩ : R.HE.H →ₗᵢ[ℂ] R.HE.H) (Tw.out x) (Tw.out y))
  ·     exact congrArg _ (LinearIsometry.inner_map_map
      (⟨R.gW j (sg0 D A3.A) g, hW j (sg0 D A3.A) g⟩ : (R.HW j (sg0 D A3.A)).H →ₗᵢ[ℂ] (R.HW j (sg0 D A3.A)).H) (Tw.out x) (Tw.out y))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtDiagSumProdPairingStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hasDerivAt_diag_eq_sum_mul_pairings : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, DifferentiableAt ℝ (fun t => M t x y) 0) →
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
      HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  first | exact @GlobalTheory.hasDerivAt_diag_sum_prod_pairing | exact GlobalTheory.hasDerivAt_diag_sum_prod_pairing | (intros; apply GlobalTheory.hasDerivAt_diag_sum_prod_pairing <;> assumption)
end

