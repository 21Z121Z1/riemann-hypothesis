import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIoLFRecIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverFormLevelInvariantMemSpanBaseForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0958
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0922
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0959
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapCommutesFieldAutomorphism
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IoConj

section General

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {c : Coeff l} (j : c.F →+* c.F) {n : ℕ}

theorem gaStar_map (hj : ∀ σ x, j (embF c σ x) = embF c σ x) (ga : Matrix (Fin n) (Fin n) E)
    (P : MvPolynomial (LtN Dw n) c.F) :
    Formalism.L2.Pj.gaStar c ga (map j P) = map j (Formalism.L2.Pj.gaStar c ga P) := by
  induction P using MvPolynomial.induction_on with
  | C x => rw [map_C, Formalism.L2.Pj.gaStar, aeval_C, aeval_C, algebraMap_eq, map_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [Formalism.L2.Pj.gaStar, aeval_X, letB, map_sum, map_mul, map_C, map_X, hj]

theorem pG_map (a : (E →+* ℂ) × ℕ → ℕ) : map j (pG (Dw := Dw) c a n) = pG (Dw := Dw) c a n := by
  have h : ∀ s i hi col, minorPolynomial (Dw := Dw) (n := n) c s i hi col = map j (minorPolynomial c s i hi col) := by
    intro s i hi col
    unfold minorPolynomial
    rw [RingHom.map_det]
    congr 1
    ext p q : 2
    simp
  symm
  unfold pG
  simp only [map_prod, map_pow]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun i _ => ?_
  congr 1
  split_ifs
  · exact h _ _ _ _
  · exact h _ _ _ _
  · rw [map_zero]

theorem rhoM_map (hj : ∀ σ x, j (embF c σ x) = embF c σ x) {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))
    (lam : Ix → DomWeight n) (ga : Matrix (Fin n) (Fin n) E) (v v' : VVc c lam)
    (h : (v' : Pol c.F Ix n) = map j (v : Pol c.F Ix n)) :
    (rhoM c (fun t => embF c (pl t)) lam ga v' : Pol c.F Ix n) =
      map j (rhoM c (fun t => embF c (pl t)) lam ga v : Pol c.F Ix n) := by
  unfold rhoM
  split_ifs with hg
  · show actP lam _ (v' : Pol c.F Ix n) = map _ (actP lam _ (v : Pol c.F Ix n))
    rw [h]
    refine GlobalTheory.IoExtend.polyAction_map _ lam _ _ (fun t => ?_) _
    refine Matrix.ext fun a b => ?_
    exact (hj (pl t) _).symm
  · simp

theorem exists_stable (hj : ∀ σ x, j (embF c σ x) = embF c σ x) {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))
    (hpl : Function.Injective pl) (hin : ∀ σ, InPsi H σ ↔ ∃ t, σ = pl t)
    (lam : Ix → DomWeight n) (a : (E →+* ℂ) × ℕ → ℕ) (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam)
    (h : IoLFRec c (fun t => embF c (pl t)) lam a io hw) :
    ∃ N : Submodule c.F (VVc c lam), hw ∈ N ∧
      (∀ ga : Matrix (Fin n) (Fin n) E, gaᴴ * ga = 1 → ∀ v ∈ N, rhoM c (fun t => embF c (pl t)) lam ga v ∈ N) ∧
      ∀ v ∈ N, ∀ v' : VVc c lam, (v' : Pol c.F Ix n) = map j (v : Pol c.F Ix n) → io v' = map j (io v) := by
  obtain ⟨hok, cga, h⟩ := h
  let e : Ix ≃ GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights.Psi H := Equiv.ofBijective (fun t => ⟨pl t, (hin _).2 ⟨t, rfl⟩⟩)
    ⟨fun s t hst => hpl (congrArg Subtype.val hst), fun σ => by
      obtain ⟨t, ht⟩ := (hin σ.1).1 σ.2
      exact ⟨t, Subtype.ext ht.symm⟩⟩
  obtain ⟨ha, d, -, hd⟩ := GlobalTheory.LFCompare.pins_of_ioLF Dw c n e a lam io hw cga hok h
  have hcga : ∀ ga : Matrix (Fin n) (Fin n) E, gaᴴ * ga = 1 → j (cga ga) = cga ga := fun ga hga => by
    rw [hd ga hga, GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights.vacChar, map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [map_zpow₀]
    exact congrArg (· ^ _) (hj _ _)
  obtain ⟨-, -, -, h4, -, -, h7, -⟩ := h
  let up : VVc c lam → VVc c lam := fun v => ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV j lam _ v.2⟩
  refine ⟨
    { carrier := {v | io (up v) = map j (io v)}
      add_mem' := fun {v w} hv hw' => ?_
      zero_mem' := ?_
      smul_mem' := fun s v hv => ?_ }, ?_, fun ga hga v hv => ?_, fun v hv v' hv' => ?_⟩
  · have e1 : up (v + w) = up v + up w := Subtype.ext (map_add (map j) _ _)
    show io (up (v + w)) = _
    rw [e1, map_add, map_add, map_add, show io (up v) = _ from hv, show io (up w) = _ from hw']
  · have e1 : up 0 = 0 := Subtype.ext (map_zero (map j))
    show io (up 0) = _
    rw [e1, map_zero, map_zero]
  · have e1 : up (s • v) = j s • up v := Subtype.ext (GlobalTheory.IoExtend.map_smul' j s _)
    show io (up (s • v)) = _
    rw [e1, map_smul, map_smul, GlobalTheory.IoExtend.map_smul', show io (up v) = _ from hv]
  · have e1 : up hw = hw := by
      apply Subtype.ext
      show map j (hw : Pol c.F Ix n) = _
      rw [show (hw : Pol c.F Ix n) = _ from hok, GlobalTheory.Proof.TensorMapDescent.map_ten]
      simp only [Formalism.L2.DIV.map_extremal]
    show io (up hw) = _
    rw [e1, h7, pG_map]
  · have e1 : up (rhoM c (fun t => embF c (pl t)) lam ga v) = rhoM c (fun t => embF c (pl t)) lam ga (up v) :=
      Subtype.ext (rhoM_map j hj pl lam ga v (up v) rfl).symm
    show io (up _) = _
    rw [e1, h4 ga hga, h4 ga hga, GlobalTheory.IoExtend.map_smul', hcga ga hga, show io (up v) = _ from hv, gaStar_map j hj]
  · rw [show v' = up v from Subtype.ext hv']
    exact hv

theorem eq_top_of_span {K X M : Type} [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup M] [Module ℂ M]
    {σ : K →+* ℂ} (c0 : X →ₛₗ[σ] M)
    (hli : ∀ (m : ℕ) (b : Fin m → X), LinearIndependent K b → LinearIndependent ℂ (fun k => c0 (b k)))
    (N : Submodule K X) (hN : Submodule.span ℂ (c0 '' (N : Set X)) = ⊤) : N = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := N.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
  obtain ⟨B, hB⟩ := GlobalTheory.AdTh.PhaseMap.exists_ext (N := ℂ) c0 hli
    { toFun := fun v => σ (f v)
      map_add' := fun v w => by rw [map_add, map_add]
      map_smul' := fun s v => by rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul] }
  replace hB : ∀ v, B (c0 v) = σ (f v) := hB
  have h1 : Submodule.span ℂ (c0 '' (N : Set X)) ≤ LinearMap.ker B := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show B (c0 v) = 0
    rw [hB, show f v = 0 from hf hv, map_zero]
  refine hf0 (LinearMap.ext fun v => ?_)
  have h2 : B (c0 v) = 0 := h1 (hN ▸ Submodule.mem_top)
  rw [hB] at h2
  exact (map_eq_zero σ).1 h2

end General

section Main

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000 in

theorem io_map_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) → M.io x' = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io x) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hfw i Tp tup O hO τ ta hta hfix x x' hx
  obtain ⟨fw⟩ := hfw
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hθ : IsInfFam R.θ := hR.models.inf
  have hc : (R.cV i).Is := hR.models.cV i
  have hP := (GlobalTheory.AdTh.RecPair.isPair_record_ofCore D G Pl0 T0 A _ R F hR i A.μ0 hO.lift.std).1
  obtain ⟨n1, n2, -, n4⟩ := GlobalTheory.AdTh.coefMap_norm_equivariant_basis_ofCore D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hO
  obtain ⟨-, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) (R.cV i) (hR.models.vpos i) hP.sigV hc
  obtain ⟨-, -, w1, -, -⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hj : ∀ σ y, (ta : O.c'.F →+* O.c'.F) (embF O.c' σ y) = embF O.c' σ y := fun σ y =>
    Subtype.ext ((hta _).trans (hfix.host σ y))
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_stable (ta : O.c'.F →+* O.c'.F) hj (tauE D) (GlobalTheory.SmoothForms.RealPts.tauE_injective D) w1
    (lamV D i) (wtA (κ i)) O.io O.hw hO.io
  haveI : FiniteDimensional O.c'.F (VsV D i O.c'.F) := Module.Finite.of_basis (Formalism.L2.DIV.bVV O.c'.F (lamV D i))
  have htop : N = ⊤ := by
    refine eq_top_of_span O.c0' n4 N ((r2 _ fun γ => ?_).resolve_left fun h0 => ?_)
    · obtain ⟨γE, -, -, h1, -, -, -, h5, -⟩ := GlobalTheory.AdTh.PhaseMap.rat_parts hθ hP.std γ
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨_, hN2 _ h5 v hv, n2 γ γE h1 v⟩
    · have h1 : O.c0' O.hw ∈ Submodule.span ℂ (O.c0' '' (N : Set _)) := Submodule.subset_span ⟨_, hN1, rfl⟩
      rw [h0, Submodule.mem_bot] at h1
      rw [h1, norm_zero] at n1
      exact zero_ne_one n1
  exact hN3 x (htop ▸ Submodule.mem_top) x' hx

end Main

end GlobalTheory.IoConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverConstantsUniqueOnDictionaryComponents
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in

theorem cc_unique_of_pinned : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ c : C.U₂.Comp → ℂ, (∀ a, Dom a (κ i).n → C.IsPinned a (κ i).n) → (∀ a, Dom a (κ i).n → ({ C with cc₂ := c } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n) → ∀ h, C.cc₂ (C.dict₂ h).1 = c (C.dict₂ h).1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hT _ _ _ _ _ _ i _ _ C hC c hP hP' h
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hr, -⟩ := hT.modelW _ hj _ hσ

  obtain ⟨a, ha, hk⟩ := GlobalTheory.T.exists_nonzero_dominant_section_each_component D T hT _ hj _ hσ (κ i).n (κ i).n_even
  set k₀ := (T.dict ((i : ℕ) + 1) T.σ₀ h).1 with hk₀
  obtain ⟨f, hf, x, hx, hne⟩ := hk k₀
  have hU := hT.unf _ hj _ hσ
  have hS := hU.2.2.2.2.1 a _ ha f hf k₀

  obtain ⟨x₁, b, hb, ho, hx₁⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E _ _ _ _
    ((T.U ((i : ℕ) + 1) T.σ₀).X k₀).Gm_herm).1 x hx
  have hne₁ : rdU (T.U ((i : ℕ) + 1) T.σ₀) f k₀ x₁ ≠ 0 := by
    rw [hx₁, hS.2.1 x hx b hb]
    exact mul_ne_zero (GlobalTheory.CoverIndep.bchar_ne_zero' _ hb) hne
  have ho' : GlobalTheory.CoverDescSpan.IsOrthFr ((T.U ((i : ℕ) + 1) T.σ₀).X k₀) x₁ := ho

  obtain ⟨u, hu, hxu⟩ := (GlobalTheory.CoverDescSpan.base_orth hT hj hσ hr hθ h).2 x₁ ho'
  obtain ⟨γ, hγ, hdu⟩ := GlobalTheory.CoverDescSpan.base_real hT hj hσ hr hθ h u hu
  rw [← hxu] at hdu
  have hne₂ : rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1
      (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).2 ≠ 0 := by
    rw [hdu]
    show rdU (T.U ((i : ℕ) + 1) T.σ₀) f k₀ (lact γ x₁) ≠ 0
    rw [hS.2.2 γ hγ x₁ ho'.mem_dom]
    refine mul_ne_zero ?_ hne₁
    obtain ⟨N, hN, hN1⟩ := ((T.U ((i : ℕ) + 1) T.σ₀).X k₀).χ_fin (laU (T.U ((i : ℕ) + 1) T.σ₀) a (κ i).n k₀)
    intro h0
    have := hN1 γ hγ
    rw [h0, zero_pow hN.ne'] at this
    exact zero_ne_one this
  have hl : ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have hphi : T.phiJ ((i : ℕ) + 1) T.σ₀ a f (h * u) ≠ 0 := by
    have eb : T.phiJ ((i : ℕ) + 1) T.σ₀ a f (h * u) = ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
        ((T.cE ((i : ℕ) + 1) T.σ₀ (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
          rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).1
            (T.dict ((i : ℕ) + 1) T.σ₀ (h * u)).2) := rfl
    rw [eb]
    refine mul_ne_zero hl (mul_ne_zero (mul_ne_zero ?_ ?_) hne₂)
    · exact norm_ne_zero_iff.1 (by rw [hT.cUnit _ hj _ hσ]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(hT.muVal _ hj _ hσ).norm]; exact one_ne_zero)

  have hcomp : (C.dict₂ (h * u)).1 = (C.dict₂ h).1 := by
    have := (GlobalTheory.CoverDescSpan.cover_real hT hj hσ hr hθ C hC h 1 u (one_mem _) hu).1
    rwa [one_mul] at this

  obtain ⟨f₂, hf₂, hpull⟩ := GlobalTheory.CovPull.exists_pull D T hT _ hj _ hσ C hC.1 a (κ i).n f hf
  have e1 := congrFun ((hP a ha).2 f hf f₂ hf₂ hpull) (h * u)
  have e2 := congrFun ((hP' a ha).2 f hf f₂ hf₂ hpull) (h * u)
  have ec : C.rd a f₂ (h * u) = ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      ((C.cc₂ (C.dict₂ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
        rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := rfl
  have ec' : ({ C with cc₂ := c } : Cover T ((i : ℕ) + 1) T.σ₀).rd a f₂ (h * u) =
      ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      ((c (C.dict₂ (h * u)).1 * T.mu ((i : ℕ) + 1) T.σ₀ (h * u)) *
        rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := rfl
  rw [ec] at e1
  rw [ec'] at e2
  have hne₃ := e1 ▸ hphi
  have hm : T.mu ((i : ℕ) + 1) T.σ₀ (h * u) ≠ 0 := by
    intro h0; rw [h0] at hne₃; simp at hne₃
  have hX : rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2 ≠ 0 := by
    intro h0; rw [h0] at hne₃; simp at hne₃
  have key := e1.trans e2.symm
  rw [← hcomp]
  have k2 : C.cc₂ (C.dict₂ (h * u)).1 * (((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      T.mu ((i : ℕ) + 1) T.σ₀ (h * u) * rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) =
      c (C.dict₂ (h * u)).1 * (((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℝ) : ℂ) *
      T.mu ((i : ℕ) + 1) T.σ₀ (h * u) * rdU C.U₂ f₂ (C.dict₂ (h * u)).1 (C.dict₂ (h * u)).2) := by
    linear_combination key
  exact mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hl hm) hX) k2

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverPullbackMemBoundedCuspidalHolomorphic
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CoverHol
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X₂.Gm u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← Matrix.one_mulVec u, ← Matrix.one_mulVec w, ← h1]
  rw [CompactEntryBounds.hermC_expand X, CompactEntryBounds.hermC_expand X₂]
  simp only [hγ, Matrix.one_mulVec]

theorem col_mul (A Y : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col (A * Y) c = A *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col Y c := by
  funext i; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem gram_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (γ.map τ * Y) = ReciprocityTheory.ChartRestriction.G.FD.gram τ X₂.Gm Y := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply]
  rw [col_mul, col_mul, hermC_move X X₂ hγ]

def majM (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p : ℕ) (hp : p ≤ r) (M : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p, ∑ b : Fin p,
    hermC τ G v (ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hp a)) *
      ((ReciprocityTheory.ChartRestriction.G.FD.gram τ G M).submatrix (Fin.castLE hp) (Fin.castLE hp))⁻¹ a b *
      conj (hermC τ G v (ReciprocityTheory.ChartRestriction.G.FD.col M (Fin.castLE hp b)))).re - (hermC τ G v v).re

theorem maj_eq (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ v = majM τ.1 X.Gm X.p0 X.p0_le (mat x τ) v := rfl

omit [NumberField E] [IsCMField E] in
theorem majM_congr (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {p q : ℕ} (hp : p ≤ r) (hq : q ≤ r) (h : p = q)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) : majM τ G p hp M v = majM τ G q hq M v := by
  subst h; rfl

theorem majM_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (τ : E →+* ℂ) {p : ℕ} (hp : p ≤ r)
    (M : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    majM τ X.Gm p hp (γ.map τ * M) (γ.map τ *ᵥ v) = majM τ X₂.Gm p hp M v := by
  unfold majM
  simp only [col_mul, hermC_move X X₂ hγ, gram_move X X₂ hγ]

theorem maj_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (hp : X.p0 = X₂.p0)
    (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ)
    (hrel : mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩) (v : Fin r → E) :
    X.maj x' ⟨τ, h₁⟩ (Data.emb τ (γ *ᵥ v)) = X₂.maj x ⟨τ, h₂⟩ (Data.emb τ v) := by
  rw [maj_eq, maj_eq, hrel, ← ReciprocityTheory.ChartRestriction.G.AR.Inst.emb_mulVec, majM_move X X₂ hγ]
  exact majM_congr _ _ _ _ hp _ _

theorem dmin_move (X X₂ : Data E r) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w)
    (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r) (τ : E →+* ℂ) (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ)
    (hrel : mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩) (i : Fin (r + 1)) :
    dmin X.Gm x' ⟨τ, h₁⟩ i = dmin X₂.Gm x ⟨τ, h₂⟩ i := by
  unfold dmin
  rw [hrel, gram_move X X₂ hγ]

theorem pnorm_move (X X₂ : Data E r) (hΨ : ∀ τ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ v w, herm X.Gm (γ *ᵥ v) (γ *ᵥ w) = herm X₂.Gm v w) (la : Wt X.Ψ r) (la₂ : Wt X₂.Ψ r)
    (hla : ∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ) i, la₂ ⟨τ, h₂⟩ i = la ⟨τ, h₁⟩ i)
    (P : Frame X.Ψ r → ℂ) (P₂ : Frame X₂.Ψ r → ℂ) (x : Frame X₂.Ψ r) (x' : Frame X.Ψ r)
    (hrel : ∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = γ.map τ * mat x ⟨τ, h₂⟩)
    (u : ℂ) (hu : ‖u‖ = 1) (hP : P₂ x = u * P x') :
    X₂.pnorm la₂ P₂ x = X.pnorm la P x' := by
  unfold Data.pnorm
  rw [hP, norm_mul, hu, one_mul]
  congr 1
  refine Fintype.prod_equiv (Equiv.subtypeEquivRight hΨ) _ _ (fun τ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h₁ : τ.1 ∈ X.Ψ := (hΨ τ.1).1 τ.2
  show _ = ‖dmin X.Gm x' ⟨τ.1, h₁⟩ i.succ / dmin X.Gm x' ⟨τ.1, h₁⟩ i.castSucc‖ ^ (-(la ⟨τ.1, h₁⟩ i : ℝ) / 2)
  rw [dmin_move X X₂ hγ x x' τ.1 τ.2 h₁ (hrel τ.1 τ.2 h₁), dmin_move X X₂ hγ x x' τ.1 τ.2 h₁ (hrel τ.1 τ.2 h₁),
    ← hla τ.1 τ.2 h₁ i]

theorem exists_firstMinimumSq_bound_of_rationalIsometry (X X₂ : Data E r) (hr : 0 < r) (hΨ : ∀ τ, τ ∈ X₂.Ψ ↔ τ ∈ X.Ψ) (γ : GL (Fin r) E)
    (hΛ : (X.Λ : Set (Fin r → E)) = (γ : Matrix (Fin r) (Fin r) E).mulVec '' (X₂.Λ : Set (Fin r → E)))
    (hγ : ∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) =
      herm X₂.Gm v w) (hp : X.p0 = X₂.p0) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ X₂.dom, ∀ x' ∈ X.dom,
      (∀ τ (h₂ : τ ∈ X₂.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩) →
      X.firstMinimumSq x' ≤ K * X₂.firstMinimumSq x := by
  set K : ℝ := 1 + ∑ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ with hKdef
  have hc2 : ∀ τ : X₂.Ψ, 0 < X₂.c τ := fun τ => IsotropicThreshold.c_pos X₂ τ
  have hKτ : ∀ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ ≤ K * X₂.c τ := by
    intro τ
    have h1 : X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ ≤ K := by
      have := Finset.single_le_sum (f := fun τ : X₂.Ψ => X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ / X₂.c τ)
        (fun τ _ => (div_pos (IsotropicThreshold.c_pos X _) (hc2 τ)).le) (Finset.mem_univ τ)
      linarith
    rwa [div_le_iff₀ (hc2 τ)] at h1
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun τ (_ : τ ∈ (Finset.univ : Finset X₂.Ψ)) =>
      (div_pos (IsotropicThreshold.c_pos X ⟨τ.1, (hΨ τ.1).1 τ.2⟩) (hc2 τ)).le)
    linarith
  refine ⟨K, hK, fun x hx x' hx' hrel => ?_⟩
  obtain ⟨w₀, hw₀, hw₀0⟩ := ReciprocityTheory.ChartRestriction.G.AR.Inst.lam_ne X₂ hr
  unfold Data.firstMinimumSq
  set S := {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x' τ (Data.emb τ.1 v)} with hS
  set S₂ := {t | ∃ v ∈ X₂.Λ, v ≠ 0 ∧ t = ∑ τ, X₂.c τ * X₂.maj x τ (Data.emb τ.1 v)} with hS₂
  have hSb : BddBelow S := ⟨0, by
    rintro _ ⟨v, -, hv0, rfl⟩
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (IsotropicThreshold.c_pos X τ).le
      (X.maj_pos hx' τ (emb_ne_zero τ.1 hv0)).le⟩
  have hS₂ne : S₂.Nonempty := ⟨_, w₀, hw₀, hw₀0, rfl⟩
  have key : sInf S / K ≤ sInf S₂ := by
    refine le_csInf hS₂ne ?_
    rintro _ ⟨w, hw, hw0, rfl⟩
    rw [div_le_iff₀ hK]
    have hγw : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ X.Λ := by
      have : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ∈ (X.Λ : Set (Fin r → E)) := by
        rw [hΛ]; exact ⟨w, hw, rfl⟩
      exact this
    have hγw0 : (γ : Matrix (Fin r) (Fin r) E) *ᵥ w ≠ 0 := by
      intro h0
      apply hw0
      have e : (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = w := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    refine (csInf_le hSb ⟨_, hγw, hγw0, rfl⟩).trans ?_
    have hre : ∑ τ : X.Ψ, X.c τ * X.maj x' τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) =
        ∑ τ : X₂.Ψ, X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ * X₂.maj x τ (Data.emb τ.1 w) := by
      refine (Fintype.sum_equiv (Equiv.subtypeEquivRight hΨ) _ _ (fun τ => ?_)).symm
      show X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ * X₂.maj x τ (Data.emb τ.1 w) = X.c ⟨τ.1, (hΨ τ.1).1 τ.2⟩ *
        X.maj x' ⟨τ.1, (hΨ τ.1).1 τ.2⟩ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w))
      rw [maj_move X X₂ hγ hp x x' τ.1 τ.2 ((hΨ τ.1).1 τ.2) (hrel τ.1 τ.2 _)]
    rw [hre, Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => ?_
    have hm := (X₂.maj_pos hx τ (emb_ne_zero τ.1 hw0)).le
    calc _ ≤ (K * X₂.c τ) * X₂.maj x τ (Data.emb τ.1 w) := mul_le_mul_of_nonneg_right (hKτ τ) hm
      _ = _ := by ring
  rwa [div_le_iff₀ hK, mul_comm] at key

theorem cover_pull_holSub0 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n) → ∀ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ → rdU C.U₂ f₂ ∈ holSub0 C.U₂.X (laU C.U₂ a n) := by
  intro D T hL j hj σ hσ C hC a n hDom f hf hfh f₂ hf₂ hP
  refine Submodule.mem_inf.2 ⟨holCusp_mem_holSub _ _ (fun k₂ => ?_), rdU_mem_offZero _ _⟩
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  have hU₁ : IsUnf (T.U j σ) := hL.unf j hj σ hσ
  have hS := Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (Submodule.mem_inf.1 hfh).1
  obtain ⟨k, γ, hΛ, hh, -, u, hu1, hx⟩ := GlobalTheory.CoverConst.cover_scalar_const D T hL j hj σ hσ C hC n k₂
  obtain ⟨hΨ, hla⟩ := GlobalTheory.CoverConst.psi_and_weight_eq D T hL j hj σ hσ C hC k₂ k
  have hp : ((T.U j σ).X k).p0 = (C.U₂.X k₂).p0 := ((hU₁.2.1 k).1).trans ((hU₂.2.1 k₂).1).symm
  let G : Frame (C.U₂.X k₂).Ψ D.R.r → Frame ((T.U j σ).X k).Ψ D.R.r := fun x τ =>
    ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, (hΨ τ.1).2 τ.2⟩ :
      Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
  have hGrel : ∀ x (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X k₂).Ψ) (h₁ : τ ∈ ((T.U j σ).X k).Ψ),
      mat (G x) ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩ :=
    fun _ _ _ _ => rfl
  have hG : ∀ x ∈ (C.U₂.X k₂).dom, G x ∈ ((T.U j σ).X k).dom ∧
      rdU C.U₂ f₂ k₂ x = u * rdU (T.U j σ) f k (G x) := fun x hxd =>
    ⟨(hx x (G x) hxd (hGrel x)).1, (hx x (G x) hxd (hGrel x)).2 a hDom f hf f₂ hf₂ hP⟩
  have hpn : ∀ x ∈ (C.U₂.X k₂).dom, (C.U₂.X k₂).pnorm (laU C.U₂ a n k₂) (rdU C.U₂ f₂ k₂) x =
      ((T.U j σ).X k).pnorm (laU (T.U j σ) a n k) (rdU (T.U j σ) f k) (G x) := fun x hxd =>
    pnorm_move _ _ hΨ hh _ _ (fun τ h₂ h₁ i => hla a n τ h₂ h₁ i) _ _ x (G x) (hGrel x) u hu1 (hG x hxd).2
  have hsec := hU₂.2.2.2.2.1 a n hDom f₂ hf₂ k₂
  obtain ⟨B, hB⟩ := (hS k).1.2
  have hbdd : (C.U₂.X k₂).IsBddSec (laU C.U₂ a n k₂) (rdU C.U₂ f₂ k₂) :=
    ⟨hsec, B, fun x hxd => (hpn x hxd).trans_le (hB _ (hG x hxd).1)⟩
  by_cases hr : 0 < D.R.r
  · obtain ⟨c₀, hc₀, hgt⟩ := ReciprocityTheory.ChartRestriction.G.FD.spectralGap_holds D.R.r _ _ _ (hS k)
    obtain ⟨C₁, hC₁⟩ := ReciprocityTheory.ChartRestriction.G.FD.cuspidalDecay_holds D.R.r _ _ _ c₀ hc₀.le hgt
    obtain ⟨K, hK, hle⟩ := exists_firstMinimumSq_bound_of_rationalIsometry _ _ hr hΨ γ hΛ hh hp
    refine GlobalTheory.CuspUnif.mem_SS_of_decay _ hr _ _ hbdd (C := |C₁|) (c := 2 * Real.pi * c₀ / K) (by positivity)
      fun x hxd => ?_
    have hGd := (hG x hxd).1
    have hl : 0 < ((T.U j σ).X k).firstMinimumSq (G x) := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom _ hr hGd)
    have hl₂ : 0 < (C.U₂.X k₂).firstMinimumSq x := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom _ hr hxd)
    have hle' := hle x hxd (G x) hGd (hGrel x)
    rw [hpn x hxd]
    refine (hC₁ (G x) hGd).trans ?_
    refine mul_le_mul (le_abs_self _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg _)
    have hq : 2 * Real.pi * c₀ / K / (C.U₂.X k₂).firstMinimumSq x ≤ 2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x) := by
      rw [div_div, div_le_div_iff₀ (by positivity) hl]
      exact mul_le_mul_of_nonneg_left hle' (by positivity)
    have e1 : -2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x) =
        -(2 * Real.pi * c₀ / ((T.U j σ).X k).firstMinimumSq (G x)) := by ring
    rw [e1, neg_div]
    exact neg_le_neg hq
  · refine ⟨hbdd, fun ξ hξ x _ => ?_⟩
    exfalso
    apply hξ.2.2
    funext i
    exact absurd i.2 (by omega)

end GlobalTheory.CoverHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalSectionBoundedNonzeroMultipleStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), Dom a n → f ∈ cusp Xo c U a n → ∃ κ : c.F, κ ≠ 0 ∧ BddAll Xo c la κ f := by
  first | exact @GlobalTheory.CuspBound.exists_bddAll_cusp | exact GlobalTheory.CuspBound.exists_bddAll_cusp | (intros; apply GlobalTheory.CuspBound.exists_bddAll_cusp <;> assumption)
end

