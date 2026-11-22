import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexEqCard
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeAct

theorem hint_mul_const {H : Type} [Group H] (K : Subgroup H) (v : H → ℂ) (c : ℂ) :
    hint K (fun z => v z * c) = hint K v * c := by
  by_cases hc : c = 0
  · subst hc
    simp [hint]
  have hS : rStab (fun z => v z * c) = rStab v := by
    ext k
    constructor
    · intro hk z
      exact mul_right_cancel₀ hc (hk z)
    · intro hk z
      show v (z * k) * c = v z * c
      rw [hk z]
  unfold hint
  rw [hS, mul_assoc]
  congr 1
  have e := smul_finsum c (fun q : H ⧸ rStab v ⊓ K => v q.out)
  simp only [smul_eq_mul] at e
  rw [mul_comm, e]
  exact finsum_congr fun q => mul_comm _ _

theorem relIndex_eq_card {G : Type} [Group G] (K K' : Subgroup G) (X : Finset G) (hXK : ∀ x ∈ X, x ∈ K)
    (hX : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') : K'.relIndex K = X.card := by
  let φ : {x // x ∈ X} → K ⧸ K'.subgroupOf K := fun x => ((⟨x.1, hXK _ x.2⟩ : K) : K ⧸ K'.subgroupOf K)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : (x.1)⁻¹ * y.1 ∈ K' := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hxy)
      exact Subtype.ext ((hX y.1 (hXK _ y.2)).unique ⟨x.2, h1⟩ ⟨y.2, by simp [K'.one_mem]⟩)
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hxX, hxk⟩, -⟩ := hX k.1 k.2
      exact ⟨⟨x, hxX⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)⟩
  show Nat.card (K ⧸ K'.subgroupOf K) = _
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem finsum_left {G : Type} [Group G] (K' : Subgroup G) (φ : G → ℂ) (hφ : ∀ g, ∀ k ∈ K', φ (g * k) = φ g) (x : G) :
    ∑ᶠ q : G ⧸ K', φ (x * q.out) = ∑ᶠ q : G ⧸ K', φ q.out := by
  refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm x : Equiv.Perm (G ⧸ K')))
  refine finsum_congr fun q => ?_
  have e : (MulAction.toPerm x : Equiv.Perm (G ⧸ K')) q = ((x * q.out : G) : G ⧸ K') := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [e]
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul K' (x * q.out)
  show φ (x * q.out) = φ ((x * q.out : G) : G ⧸ K').out
  rw [hs, hφ _ _ s.2]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ind_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GLw a w × GLw b w) W)
    (u : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom))
    (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (g : GLw n w) :
    u.1.1 (blk h w m Y * g) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) • ρ m (u.1.1 g) := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ = GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) (GlobalTheory.LeviFubini.levH_blk h w m Y)
    simpa [GlobalTheory.LeviFubini.levH] using this
  have := GlobalTheory.SmGL.parInd_law _ _ u ⟨blk h w m Y, GlobalTheory.LeviFubini.blk_mem h w m Y⟩ g
  rw [hl] at this
  rw [GlobalTheory.AbsHalfLevi.absHalf_det_div_eq_deltaHalf E a b w m]
  simpa using this

theorem hk_ind_apply : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GLw a w × GLw b w) W), ∀ (f : GLw n w → ℂ), IsHk K' f → ∀ u ∈ fixed (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K', ∀ x ∈ X, ∀ lw : W →ₗ[ℂ] ℂ, lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) fun m => phi3 h w f x y m * lw (ρ m (u.1.1 y)) := by
  intro E _ _ _ n a b h w K' hopen hle hnorm X hXK hX W _ _ ρ f hf u hu x hx lw
  have hfr : ∀ g, ∀ k ∈ K', f (g * k) = f g := fun g k hk => by
    simpa using hf.2.2.2 1 K'.one_mem k hk g
  have hur : ∀ g, ∀ k ∈ K', u.1.1 (g * k) = u.1.1 g := fun g k hk => by
    have h1 : GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ k u = u := (hu ⟨k, hk⟩).trans (one_smul ℂ u)
    exact congrArg (fun v : GlobalTheory.SmGL.IndSp _ _ => v.1.1 g) h1

  set φ : GLw n w → ℂ := fun g => f (x⁻¹ * g) * lw (u.1.1 g) with hφdef
  have hφr : ∀ g, ∀ k ∈ K', φ (g * k) = φ g := fun g k hk => by
    simp only [hφdef]
    rw [← mul_assoc, hfr _ k hk, hur g k hk]
  have hφc : HasCompactSupport φ := by
    have h1 : HasCompactSupport fun g => f (x⁻¹ * g) := hf.2.2.1.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
    exact h1.mul_right
  have hcard : K'.relIndex (GlobalTheory.LFun.KGL w n) = X.card := relIndex_eq_card _ K' X hXK hX
  have hX0 : X.card ≠ 0 := by
    obtain ⟨z, ⟨hz, -⟩, -⟩ := hX 1 (GlobalTheory.LFun.KGL w n).one_mem
    exact (Finset.card_pos.2 ⟨z, hz⟩).ne'
  have hX0' : (X.card : ℂ) ≠ 0 := by exact_mod_cast hX0

  let Ψ : GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))
      (ρ.comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] ℂ :=
    { toFun := fun v => lw (v.1.1 x)
      map_add' := fun v v' => map_add lw _ _
      map_smul' := fun c v => map_smul lw c _ }
  have hfin := GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen f hf.2.2.1
  have e1 : lw ((hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u).1.1 x) = ∑ᶠ q : GLw n w ⧸ K', φ (x * q.out) := by
    show Ψ (hk (GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ) K' f u) = _
    unfold hk
    refine (Ψ.toAddMonoidHom.map_finsum (hfin.subset fun q hq h0 => hq (by
      have h0' : f q.out = 0 := h0
      show f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u = 0
      rw [h0', zero_smul]))).trans ?_
    refine finsum_congr fun q => ?_
    show Ψ (f q.out • GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) ρ q.out u) = _
    rw [map_smul]
    simp only [hφdef, inv_mul_cancel_left]
    rfl
  have e2 := GlobalTheory.CompanionTheory.HintSmaller.hint_eq_of_le (GlobalTheory.LFun.KGL w n) K' φ hle (fun k hk g => hφr g k hk)
    (by rw [hcard]; exact hX0) (GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K' hopen φ hφc)
  have e3 := GlobalTheory.T.hecke_coset_sum_compact E n a b h w K' hopen hle hnorm X hXK hX φ hφr hφc
  rw [hcard] at e2
  have e4 : ∑ᶠ q : GLw n w ⧸ K', φ q.out =
      ∑ y ∈ X, hint ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) fun m =>
        hint (intMat a b w) fun Y => φ (blk h w m (Multiplicative.toAdd Y) * y) := by
    have := e2.symm.trans e3
    exact mul_left_cancel₀ (inv_ne_zero hX0') this
  rw [e1, finsum_left K' φ hφr x, e4]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  funext m
  have e5 : (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      φ (blk h w m (Multiplicative.toAdd Y) * y)) = fun Y =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y) *
        (absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) * lw (ρ m (u.1.1 y))) := by
    funext Y
    simp only [hφdef]
    rw [ind_blk h w ρ u m _ y, map_smul, smul_eq_mul, mul_assoc]
  rw [e5, hint_mul_const]
  unfold phi3
  ring

end GlobalTheory.CompanionTheory.HeckeAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldMapPtCoordSndM
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.FnDeg

open GlobalTheory.ProjSpace

theorem eval_pullRatio_comp {X Y : Scheme.{0}} {N : ℕ} (g : X ⟶ Y) (ψ : Y ⟶ PSpace ℤ N) (x : X)
    (i : Fin (N + 1)) (hx : g x ∈ ψ ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    (g.residueFieldMap x).hom ((Y.evaluation (ψ ⁻¹ᵁ chart ℤ N i) (g x) hx).hom (pullRatio ψ _ i le_rfl j)) =
      (X.evaluation ((g ≫ ψ) ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio (g ≫ ψ) _ i le_rfl j) := by
  have h1 := Scheme.evaluation_naturality_apply g x hx (pullRatio ψ _ i le_rfl j)
  have h2 : g.app (ψ ⁻¹ᵁ chart ℤ N i) (pullRatio ψ _ i le_rfl j) = pullRatio (g ≫ ψ) _ i le_rfl j := by
    rw [Scheme.Hom.app_eq_appLE]
    exact appLE_pullRatio (hi := le_rfl) g le_rfl
  exact h1.trans (congrArg _ h2)

theorem closure_eval_ratio {N : ℕ} (p : PSpace ℤ N) (i : Fin (N + 1)) (hp : p ∈ chart ℤ N i) :
    Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j)) = ⊤ := by
  set K := Subfield.closure (Set.range fun j => ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom (ratio ℤ N i j))
  have hmem : ∀ s, ((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom s ∈ K := by
    intro s
    obtain ⟨q, rfl⟩ := aeval_ratio_surjective ℤ N i s
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [aeval_C]
      simpa using K.intCast_mem a
    | add a b ha hb =>
      rw [map_add, map_add]
      exact K.add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul, map_mul, aeval_X]
      exact K.mul_mem ha (Subfield.subset_closure ⟨j, rfl⟩)
  let ρ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (R := Γ(PSpace ℤ N, chart ℤ N i)) (S := K)
      (((PSpace ℤ N).evaluation (chart ℤ N i) p hp).hom.codRestrict K hmem)
  refine GlobalTheory.subfield_eq_top_of_fromSpecResidueField_factors _ p K
    (Spec.map ρ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ?_
  rw [← Category.assoc, ← Spec.map_comp]
  have hev : Spec.map ((PSpace ℤ N).evaluation (chart ℤ N i) p hp) ≫ (isAffineOpen_chart ℤ N i).fromSpec =
      (PSpace ℤ N).fromSpecResidueField p := by
    rw [Scheme.fromSpecResidueField, ← (isAffineOpen_chart ℤ N i).fromSpecStalk_eq_fromSpecStalk hp,
      IsAffineOpen.fromSpecStalk, Scheme.evaluation, Spec.map_comp, Category.assoc]
  exact hev

theorem range_residueFieldMap_le {X : Scheme.{0}} {N : ℕ} (φ : X ⟶ PSpace ℤ N) (x : X) (i : Fin (N + 1))
    (hx : x ∈ φ ⁻¹ᵁ chart ℤ N i) :
    Set.range (φ.residueFieldMap x).hom ⊆
      Subfield.closure (Set.range fun j => (X.evaluation (φ ⁻¹ᵁ chart ℤ N i) x hx).hom (pullRatio φ _ i le_rfl j)) := by
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Subfield.closure (Set.range fun j =>
      ((PSpace ℤ N).evaluation (chart ℤ N i) (φ x) hx).hom (ratio ℤ N i j)) := by
    have hc := closure_eval_ratio (φ x) i hx
    rw [hc]
    exact Subfield.mem_top a
  have h1 : (φ.residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
  rw [RingHom.map_field_closure] at h1
  refine Subfield.closure_mono ?_ h1
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨j, ?_⟩
  have h2 := Scheme.evaluation_naturality_apply φ x hx (ratio ℤ N i j)
  rw [Scheme.Hom.app_eq_appLE] at h2
  exact h2.symm

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
  simp only [ptCoord, pullRatio_self, map_one]

theorem range_prB_le (x : MP ℤ m n) (k : Fin (m + 1)) :
    Set.range ((prB n k).residueFieldMap x).hom ⊆ Subfield.closure (Set.range (ptCoord x)) := by
  refine (range_residueFieldMap_le (prB n k) x (ptChart x k) (mem_ptChart x k)).trans ?_
  refine Subfield.closure_le.2 ?_
  rintro _ ⟨j, rfl⟩
  exact Subfield.subset_closure ⟨⟨k, j⟩, rfl⟩

abbrev sndM (m : ℕ) (n : Fin (m + 2) → ℕ) : MP ℤ (m + 1) n ⟶ MP ℤ m (Fin.tail n) :=
  pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))

theorem residueFieldMap_ptCoord_sndM {n : Fin (m + 2) → ℕ} (x : MP ℤ (m + 1) n) (k : Fin (m + 1))
    (j : Bk (Fin.tail n) k) :
    ((sndM m n).residueFieldMap x).hom (ptCoord (sndM m n x) ⟨k, j⟩) = ptCoord x ⟨k.succ, j⟩ :=
  eval_pullRatio_comp (sndM m n) (prB (Fin.tail n) k) x (ptChart (sndM m n x) k) (mem_ptChart (sndM m n x) k) j

theorem closure_ptCoord : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n),
    Subfield.closure (Set.range (ptCoord x)) = ⊤
  | 0, n, x => by
    haveI : IsOpenImmersion (prB n 0) := inferInstanceAs (IsOpenImmersion (𝟙 _))
    refine eq_top_iff.2 fun a _ => range_prB_le x 0 ?_
    exact (ConcreteCategory.bijective_of_isIso ((prB n 0).residueFieldMap x)).2 a
  | m + 1, n, x => by
    have H : Subfield.closure (Set.range ((prB n 0).residueFieldMap x).hom ∪
        Set.range ((sndM m n).residueFieldMap x).hom) = ⊤ :=
      GlobalTheory.closure_range_residueFieldMap_pullback_eq_top _ _ _ (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) x
    rw [eq_top_iff, ← H]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact range_prB_le x 0 ⟨a, rfl⟩
    · rintro _ ⟨a, rfl⟩
      have ha : a ∈ Subfield.closure (Set.range (ptCoord (sndM m n x))) := by
        rw [closure_ptCoord m (Fin.tail n) (sndM m n x)]
        exact Subfield.mem_top a
      have h1 : ((sndM m n).residueFieldMap x).hom a ∈ _ := Subfield.mem_map.2 ⟨a, ha, rfl⟩
      rw [RingHom.map_field_closure] at h1
      refine Subfield.closure_mono ?_ h1
      rintro _ ⟨_, ⟨⟨k, j⟩, rfl⟩, rfl⟩
      exact ⟨⟨k.succ, j⟩, (residueFieldMap_ptCoord_sndM x k j).symm⟩

theorem blockFnField_ptCoord (x : MP ℤ m n) [CharZero ((MP ℤ m n).residueField x)] :
    blockFnField (ptCoord x) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  have hle : Subfield.closure (Set.range (ptCoord x)) ≤ (blockFnField (ptCoord x)).toSubfield := by
    refine Subfield.closure_le.2 ?_
    rintro _ ⟨p, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, ?_⟩
    rw [ptCoord_ptChart, div_one]
  exact hle (by rw [closure_ptCoord]; exact Subfield.mem_top a)

theorem blockFnField_comp {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω Ω' : Type*} [Field Ω]
    [CharZero Ω] [Field Ω'] [CharZero Ω'] (g : Ω →ₐ[ℚ] Ω') (y : (Σ k, ι k) → Ω) :
    blockFnField (g ∘ y) = (blockFnField y).map g := by
  unfold blockFnField
  rw [IntermediateField.adjoin_map]
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, h, rfl⟩
    exact ⟨_, ⟨p, q, h, rfl⟩, by simp [map_div₀]⟩
  · rintro ⟨_, ⟨p, q, h, rfl⟩, rfl⟩
    exact ⟨p, q, h, by simp [map_div₀]⟩

theorem ptCoord_sv (n' : ℕ) {m : ℕ} (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (p : Σ k, Bk n k) :
    ptCoord x (sv n' n p) = ((qpSnd n' m n).residueFieldMap x).hom (ptCoord ((qpSnd n' m n) x) p) :=
  (residueFieldMap_ptCoord_sndM (n := consN n' n) x p.1 p.2).symm

theorem relfinrank_blockFnField_sv : ∀ (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n))
    [CharZero ((MP ℤ (m + 1) (consN n' n)).residueField x)],
    IntermediateField.relfinrank (blockFnField (ptCoord x ∘ sv n' n)) (blockFnField (ptCoord x)) =
      (qpSnd n' m n).residueDegree x := by
  intro n' m n x _
  let f : (MP ℤ m n).residueField ((qpSnd n' m n) x) ⟶ (MP ℤ (m + 1) (consN n' n)).residueField x :=
    (qpSnd n' m n).residueFieldMap x
  haveI : CharZero ((MP ℤ m n).residueField ((qpSnd n' m n) x)) :=
    (RingHom.charZero_iff f.hom.injective).2 inferInstance
  let g := f.hom.toRatAlgHom
  have e : ptCoord x ∘ sv n' n = g ∘ ptCoord ((qpSnd n' m n) x) := _root_.funext fun p => ptCoord_sv n' n x p
  rw [e, blockFnField_comp, blockFnField_ptCoord, blockFnField_ptCoord, IntermediateField.relfinrank_top_right]
  letI := f.hom.toAlgebra
  let i := (IntermediateField.topEquiv.symm.trans (IntermediateField.equivMap ⊤ g)).toRingEquiv
  refine (Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) ?_).symm
  ext a
  rfl

end GlobalTheory.CompanionTheory.MPDict.FnDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilIntegralNormalised
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (fouH σ ψ db τ) db → (∀ z, ∫ y, fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∫ y, fouH σ ψ db τ y * (starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ dx hdx db hdb Φ hΦ τ hτ hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, hTr, -, hB, hCl, hG⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : LocallyCompactSpace (HermR (AF F) σ n) := (hCl n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR (AF F) σ n) :=
    (hCl n).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have := hdx.1
  have := hdb.1
  have : SFinite dx := inferInstance
  have : SFinite db := inferInstance
  set Th := fouH σ ψ db τ with hTh
  set S : HermR (AF F) σ n := hermOf (AF F) σ T hT with hS
  obtain ⟨hψc, hψn, -⟩ := hψ

  have hstar : ∀ (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E),
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) := by
    intro y x
    simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rfl
  have hchi : ∀ y : HermR (AF F) σ n, chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y S) := by
    intro y
    have e : Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) =
        ∑ a, ∑ b, (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a := by
      rw [Matrix.trace_mul_comm]
      rfl
    rw [chiT, e]
    rfl
  have hsub : ∀ y z w : HermR (AF F) σ n,
      pairHerm (AF F) σ n y z + -pairHerm (AF F) σ n y w = pairHerm (AF F) σ n y (z - w) := by
    intro y z w
    simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]
    ring
  have hpc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S) := by
    have hg : Continuous (gramR (AF F) σ J : (Fin n → Fin M → AF F ⊗[F] E) → _) := hG n M J
    show Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ a, ∑ b, (z.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (gramR (AF F) σ J z.2 b a - (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a))
    refine continuous_const.mul (hTr.comp (continuous_finset_sum _ fun a _ =>
      continuous_finset_sum _ fun b _ => ?_))
    exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
      (((hg.comp continuous_snd).matrix_elem b a).sub continuous_const)
  have hint : Integrable (Function.uncurry fun (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) =>
      Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S)))) (db.prod dx) := by
    have h0 : Integrable (fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) => Th z.1 * Φ z.2)
        (db.prod dx) := hτ.mul_prod hΦ
    have hc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S)) := hψc.comp hpc
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have := h0.aestronglyMeasurable.mul hc.aestronglyMeasurable
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hψn, mul_one, le_refl]
  have hL : ∀ y, Th y * (starN σ J ψ dx Φ y * chiT σ ψ T y) =
      ∫ x, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂dx := by
    intro y
    rw [integral_const_mul, starN, ← integral_mul_const, hchi]
    congr 2
    funext x
    rw [hstar, mul_assoc, ← AddChar.map_add_eq_mul, hsub]
  have hR : ∀ x, ∫ y, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂db =
      Φ x * τ (S - gramH hCM hJ (AF F) x) := by
    intro x
    have := hinv (gramH hCM hJ (AF F) x - S)
    rw [neg_sub] at this
    rw [← this, ← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL]
  rw [integral_integral_swap hint]
  simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVecCompleteOfUnitary
section
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob Filter
open GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped Topology

namespace GlobalTheory.CompanionTheory.SobComplete

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Dw_sub_of_sm {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x) (hy : Sm ε σ y) :
    Dw σ l (x - y) = Dw σ l x - Dw σ l y := by
  have hxy : Sm ε σ (x - y) := sm_iff.2 (Submodule.sub_mem _ (sm_iff.1 hx) (sm_iff.1 hy))
  have h := Dw_add hσ hl hxy hy
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem tendsto_sobNorm_zero {σ : Mx n → (H →L[ℂ] H)} {u : ℕ → H} (S : List (List (Mx n)))
    (h : ∀ l ∈ S, Tendsto (fun k => ‖l.foldr (dRep σ) (u k)‖) atTop (𝓝 0)) :
    Tendsto (fun k => sobNorm σ S (u k)) atTop (𝓝 0) := by
  induction S with
  | nil => simpa [sobNorm] using tendsto_const_nhds
  | cons l S ih =>
    have h1 := h l List.mem_cons_self
    have h2 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun k => ?_
    simp [sobNorm]

theorem smoothVec_complete_of_unitary (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UJset ε) σ) (w : ℕ → H) (hw : ∀ k, SmoothVec (lieSet ε) σ (w k))
    (hC : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0,
      ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) :
    ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)),
      (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Tendsto (fun k => sobNorm σ S (w k - w₀)) atTop (𝓝 0) := by
  have hρ : ModRep ε σ := GlobalTheory.FamSmooth.modRep_of_isURepOn hσ
  have hmem : ∀ l : List (lie (Jm ε)), ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε := fun l X hX => by
    obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
    exact Y.2
  let U : ℕ → List (lie (Jm ε)) → H := fun k l => Dw σ (l.map Subtype.val) (w k)
  have hU : ∀ k, U k ∈ Fam ε σ := fun k => GlobalTheory.SobUnif.smooth_fam hσ (hw k)
  have hcau : ∀ l, CauchySeq fun k => U k l := fun l => by
    refine Metric.cauchySeq_iff.2 fun δ hδ => ?_
    obtain ⟨K, hK⟩ := hC [l.map Subtype.val] (by simpa using hmem l) δ hδ
    refine ⟨K, fun k hk m hm => ?_⟩
    rw [dist_eq_norm]
    show ‖Dw σ (l.map Subtype.val) (w k) - Dw σ (l.map Subtype.val) (w m)‖ < δ
    rw [← Dw_sub_of_sm hσ (hmem l) (hw k) (hw m)]
    exact (norm_Dw_le_sobNorm σ List.mem_cons_self _).trans_lt (hK k hk m hm)
  choose v hv using fun l => cauchySeq_tendsto_of_complete (hcau l)
  have hvF : v ∈ Fam ε σ :=
    (GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth n ε H σ hρ).mem_of_tendsto (tendsto_pi_nhds.2 hv) (Eventually.of_forall hU)
  obtain ⟨hs, hd⟩ := GlobalTheory.SobUnif.fam_smooth hσ hvF
  refine ⟨v [], hs, fun S hS => tendsto_sobNorm_zero S fun l hl => ?_⟩
  obtain ⟨l', rfl⟩ := GlobalTheory.SobUnif.exists_lift l (hS l hl)
  have h1 : Tendsto (fun k => U k l' - v l') atTop (𝓝 0) := by
    simpa using (hv l').sub_const (v l')
  have h2 := h1.norm
  rw [norm_zero] at h2
  refine h2.congr fun k => ?_
  show ‖Dw σ (l'.map Subtype.val) (w k) - v l'‖ = ‖Dw σ (l'.map Subtype.val) (w k - v [])‖
  rw [Dw_sub_of_sm hσ (hmem l') (hw k) hs, hd l']

theorem smoothVec_complete : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ w : ℕ → H, (∀ k, SmoothVec (lieSet ε) σ (w k)) → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) → ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Filter.Tendsto (fun k => sobNorm σ S (w k - w₀)) Filter.atTop (nhds 0) :=
  fun n ε H _ _ _ σ hσ _ w hw hC => smoothVec_complete_of_unitary n ε H σ hσ w hw hC

end GlobalTheory.CompanionTheory.SobComplete

end
end

