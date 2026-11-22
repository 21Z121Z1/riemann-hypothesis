import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0182
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0184
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0187
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SqCSmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

theorem sqC_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (T : C') (x : sqM a b (m.G.obj T)) :
    (m.sqC c'' ha'' hb'').τ T x = (m.sqC c ha hb).τ T x + (m.sqC c' ha' hb').τ T x := by
  subst hc
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (c + c') * m.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y) + Ideal.Quotient.mk _ (algebraMap R' _ c' * m.ρ T y)
  rw [map_add, add_mul, map_add]

theorem sqC_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b') (T : C')
    (x : sqM a b (m.G.obj T)) :
    (m.sqC c' ha' hb').τ T x = (m.sqC c ha hb).τ T (r • x) := by
  subst hc
  rw [LinearMap.map_smulₛₗ]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (σ r * c) * m.ρ T y) =
    σ r • Ideal.Quotient.mk _ (algebraMap R' _ c * m.ρ T y)
  have h : ∀ z : Φ'.A.obj T, Ideal.Quotient.mk (b'.S T) (algebraMap R' _ (σ r) * z) = σ r • Ideal.Quotient.mk (b'.S T) z :=
    fun z => by rw [← Algebra.smul_def]; rfl
  rw [← h, ← mul_assoc, ← map_mul]

section Pts

variable {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D)

theorem mPt_add {c c' c'' : R'} (hc : c'' = c + c') {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (ha'' : m.LeC c'' a a') (hb'' : m.LeC c'' b b') (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c'' ha'' hb'').pull j x = (mPt m E E' e c ha hb).pull j x + (mPt m E E' e c' ha' hb').pull j x := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c'' ha'' hb'').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom f hf
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  change (mPt m E E' e c'' ha'' hb'').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _ + (mPt m E E' e c' ha' hb').hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j f hf h2, CrystallineSemistableComparison.P.mapH_cls _ j f hf h3,
    ← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.1 _ _ h2 h3 (by rw [map_add, h2, h3, add_zero])]
  exact cls_congr (funext fun s => sqC_add m hc ha hb ha' hb' ha'' hb'' _ _) _ _

theorem mPt_smul {c c' : R'} (r : R) (hc : c' = σ r * c) {a b : IdF Φ.A} {a' b' : IdF Φ'.A}
    (ha : m.LeC c a a') (hb : m.LeC c b b') (ha' : m.LeC c' a a') (hb' : m.LeC c' b b')
    (j : ℕ) (x : CH.H (Pt.U E ⋙ sq a b) j) :
    (mPt m E E' e c' ha' hb').pull j x = (mPt m E E' e c ha hb).pull j (r • x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  have h0 : CH.d _ j (r • f) = 0 := by rw [map_smul]; exact (show r • CH.d _ j f = 0 by rw [show CH.d _ j f = 0 from hf, smul_zero])
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c' ha' hb').hom f hf
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc (mPt m E E' e c ha hb).hom (r • f) h0
  rw [← (CrystallineSemistableComparison.P.cls_surj _ j).2.2.2.2 r f hf h0]
  change (mPt m E E' e c' ha' hb').hom.mapH j _ = (mPt m E E' e c ha hb).hom.mapH j _
  rw [CrystallineSemistableComparison.P.mapH_cls _ j f hf h1, CrystallineSemistableComparison.P.mapH_cls _ j _ h0 h2]
  exact cls_congr (funext fun s => sqC_smul m r hc ha hb ha' hb' _ _) _ _

theorem pull_U (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (j : ℕ)
    (x : CH.H (sq a b) j) :
    (mPt m E E' e c ha hb).pull j ((CH.Mor.restrict (sq a b) (Pt.U E)).pull j x) =
      (CH.Mor.restrict (sq a' b') (Pt.U E')).pull j ((m.sqC c ha hb).pull j x) := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx _) j).1 x
  rfl

end Pts

section HAdd

variable {R'' : Type} [CommRing R''] [Algebra R R''] {Ψ : PDF R'' C'} (p : SMor Φ Ψ (algebraMap R R''))
  {d : ℕ} (E : Frame Φ d) (E' : Frame Ψ d) (e : E.D ⟶ p.G.obj E'.D)

theorem hadd_Pt {N : Type} [AddCommGroup N] [Module R N] (ν : N →ₗ[R] R'') {a b : IdF Φ.A} {a' b' : IdF Ψ.A}
    (ha : ∀ n, p.LeC (ν n) a a') (hb : ∀ n, p.LeC (ν n) b b') (j : ℕ) :
    ∃ F : N ⊗[R] CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j,
      ∀ n x, F (n ⊗ₜ x) = (mPt p E E' e (ν n) (ha n) (hb n)).pull j x := by
  let f : N →+ (CH.H (Pt.U E ⋙ sq a b) j →+ CH.H (Pt.U E' ⋙ sq a' b') j) :=
    AddMonoidHom.mk' (fun n => ((mPt p E E' e (ν n) (ha n) (hb n)).pull j).toAddMonoidHom) (fun n n' => AddMonoidHom.ext fun x =>
      mPt_add p E E' e (map_add ν n n') (ha n) (hb n) (ha n') (hb n') (ha _) (hb _) j x)
  refine ⟨TensorProduct.liftAddHom f fun r n x => ?_, fun n x => ?_⟩
  · exact mPt_smul p E E' e r (by rw [map_smul, Algebra.smul_def]) (ha n) (hb n) (ha _) (hb _) j x
  · exact TensorProduct.liftAddHom_tmul _ _ _ _

end HAdd

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalK
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing Pointwise
open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

namespace GlobalTheory.CompanionTheory.EisTestK

theorem nhd_choice {K K₀ : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [Group K₀] [TopologicalSpace K₀] [IsTopologicalGroup K₀] [CompactSpace K₀] [T2Space K₀]
    (j : K →* K₀) (hj : Continuous j) (S : Subgroup K₀) (hS : IsClosed (S : Set K₀))
    (N₁ : Set K₀) (hN : N₁ ∈ 𝓝 (1 : K₀)) (V : Set K) (hV : V ∈ 𝓝 (1 : K)) :
    ∃ U ∈ 𝓝 (1 : K₀), ∀ (κ : K) (p u : K₀), p ∈ S → u ∈ U → j κ = p * u →
      ∃ r v : K, j r ∈ S ∧ v ∈ V ∧ κ = r * v ∧ ∀ u' ∈ U, j v * u'⁻¹ ∈ N₁ := by
  have hcont : Tendsto (fun x : K₀ × K₀ => x.1 * x.2⁻¹) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1) := by
    have h : Continuous (fun x : K₀ × K₀ => x.1 * x.2⁻¹) := by fun_prop
    have := h.tendsto ((1 : K₀), (1 : K₀))
    simpa [nhds_prod_eq] using this
  obtain ⟨W, hW, hWN⟩ := Filter.mem_prod_self_iff.1 (hcont hN)
  have hjW : j ⁻¹' W ∈ 𝓝 (1 : K) := hj.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨V₀, hV₀sub, hV₀o, h1⟩ := mem_nhds_iff.1 (Filter.inter_mem hV hjW)
  let Q : Subgroup K := S.comap j
  let A : Set K := (Q : Set K) * V₀
  have hAo : IsOpen A := hV₀o.mul_left
  have hC : IsCompact (j '' Aᶜ) := (hAo.isClosed_compl.isCompact).image hj
  have hScpt : IsCompact (S : Set K₀) := hS.isCompact
  let T : Set K₀ := (S : Set K₀) * (j '' Aᶜ)
  have hT : IsCompact T := hScpt.mul hC
  have h1T : (1 : K₀) ∉ T := by
    rintro ⟨p, hp, c, ⟨x, hx, rfl⟩, hpc⟩
    apply hx
    have hjx : j x ∈ S := by
      have : j x = p⁻¹ := eq_inv_of_mul_eq_one_right hpc
      rw [this]; exact S.inv_mem hp
    exact ⟨x, hjx, 1, h1, by simp⟩
  refine ⟨W ∩ Tᶜ, Filter.inter_mem hW (hT.isClosed.isOpen_compl.mem_nhds h1T), ?_⟩
  intro κ p u hp hu hκ
  by_cases hκA : κ ∈ A
  · obtain ⟨r, hr, v, hv, rfl⟩ := hκA
    refine ⟨r, v, hr, (hV₀sub hv).1, rfl, fun u' hu' => ?_⟩
    exact hWN (Set.mk_mem_prod (hV₀sub hv).2 hu'.1)
  · exfalso
    apply hu.2
    refine ⟨p⁻¹, S.inv_mem hp, j κ, ⟨κ, hκA, rfl⟩, ?_⟩
    simp [hκ]

section Concrete

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]

theorem dgl_mem_stab (d : ι → IdeleGroup k) (i : ι) : dgl d ∈ stab 𝔸[k] ({i} : Set ι) := by
  intro r hr c hc
  have hrc : r ≠ c := fun h => hr (h ▸ hc)
  exact ⟨Matrix.diagonal_apply_ne _ hrc, Matrix.diagonal_apply_ne _ hrc⟩

theorem kap_mem_stab_iff (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    kap π d g ∈ stab 𝔸[k] ({i} : Set ι) ↔ π g ∈ stab 𝔸[k] ({i} : Set ι) := by
  have hD := dgl_mem_stab d i
  constructor
  · intro h
    have e : π g = dgl d * kap π d g * (dgl d)⁻¹ := by simp [kap, mul_assoc]
    rw [e]
    exact mul_mem (mul_mem hD h) (inv_mem hD)
  · intro h
    exact mul_mem (mul_mem (inv_mem hD) h) hD

theorem bdet_congr {R : Type} [CommRing R] {s : Set ι} {g g' : GL ι R}
    (h : (g : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι) =
      (g' : Matrix ι ι R).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) : bdet s g = bdet s g' := by
  unfold bdet
  split_ifs with h1 h2 h2
  · exact Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h])
  · exact absurd (by rwa [h] at h1) h2
  · exact absurd (by rwa [← h] at h2) h1
  · rfl

theorem bdet_kap (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι) (g : G) :
    bdet ({i} : Set ι) (kap π d g) = bdet ({i} : Set ι) (π g) := by
  apply bdet_congr
  ext ⟨a, ha⟩ ⟨b, hb⟩
  obtain rfl : a = i := ha
  obtain rfl : b = a := hb
  have e : (((dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) =
      Matrix.diagonal fun i => (((d i)⁻¹ : IdeleGroup k) : 𝔸[k]) := rfl
  have e' : ((dgl d : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) = Matrix.diagonal fun i => (d i : 𝔸[k]) := rfl
  simp only [Matrix.submatrix_apply, kap, Units.val_mul, e, e', Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [mul_right_comm, Units.inv_mul, one_mul]

end Concrete

theorem testK : StdGood → BdetLaw → TestFun → TestK := by
  intro hStd hB hT G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hSide V hV
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : CompactSpace ((adStd k).kGL ι) := isCompact_iff_compactSpace.1 ((hStd k).kcpt ι)
  obtain ⟨hcl, hmul, hcb, -, -, -⟩ := hB k 𝔸[k] (adStd k) (hStd k) ι ({i} : Set ι)
  let j : K →* (adStd k).kGL ι :=
    { toFun := fun κ => ⟨kap π d κ, hSide.piK κ κ.2⟩
      map_one' := by apply Subtype.ext; simp [kap]
      map_mul' := fun a b => by apply Subtype.ext; simp [kap, mul_assoc] }
  have hj : Continuous j := by
    refine Continuous.subtype_mk ?_ _
    unfold kap
    exact (continuous_const.mul (hSide.cont.comp continuous_subtype_val)).mul continuous_const
  let S : Subgroup ((adStd k).kGL ι) := (stab 𝔸[k] ({i} : Set ι)).comap ((adStd k).kGL ι).subtype
  have hS : IsClosed (S : Set ((adStd k).kGL ι)) := hcl.preimage continuous_subtype_val
  have hb1 : bdet ({i} : Set ι) (1 : GL ι 𝔸[k]) = 1 := by
    have := hmul 1 (one_mem _) 1 (one_mem _)
    simpa using this
  let f : (adStd k).kGL ι → ℂ := fun p => (ω.toIdele (bdet ({i} : Set ι) p.1) : ℂ)
  have hf1 : f 1 = 1 := by
    show (ω.toIdele (bdet ({i} : Set ι) (1 : GL ι 𝔸[k])) : ℂ) = 1
    rw [hb1]
    simp [HeckeCharacter.toIdele_apply]
  have hfc : ContinuousOn f (S : Set ((adStd k).kGL ι)) := by
    have h1 : ContinuousOn (fun p : (adStd k).kGL ι => bdet ({i} : Set ι) p.1) (S : Set ((adStd k).kGL ι)) :=
      hcb.comp continuous_subtype_val.continuousOn fun p hp => hp
    exact continuous_subtype_val.comp_continuousOn (ω.continuous_toIdele.comp_continuousOn h1)
  obtain ⟨N₁, hN₁, hNf⟩ : ∃ N₁ ∈ 𝓝 (1 : (adStd k).kGL ι), ∀ p ∈ S, p ∈ N₁ → ‖f p - 1‖ ≤ 1 / 4 := by
    have h := hfc 1 (one_mem S)
    have hm : f ⁻¹' Metric.closedBall 1 (1 / 4) ∈ 𝓝[(S : Set ((adStd k).kGL ι))] (1 : (adStd k).kGL ι) :=
      h (by rw [hf1]; exact Metric.closedBall_mem_nhds _ (by norm_num))
    obtain ⟨u, huo, hu1, hus⟩ := mem_nhdsWithin.1 hm
    refine ⟨u, huo.mem_nhds hu1, fun p hp hpu => ?_⟩
    have := hus ⟨hpu, hp⟩
    simpa [dist_eq_norm] using this
  obtain ⟨U, hU, hUmain⟩ := nhd_choice j hj S hS N₁ hN₁ V hV
  obtain ⟨Ψ, Ψ₁, ψ, hΨ, hΨ₁, hψc, hψ1, hfac, hsupp, hlaw, hz, hone⟩ := hT k ι i ω hSide.sq U hU
  refine ⟨Ψ, Ψ₁, ψ ∘ j, hΨ, hΨ₁, hψc.comp hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hψ1
  · intro r κ hr
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := (kap_mem_stab_iff π d i r).2 ((hSide.mem _).1 hr)
    show ψ (j (r * κ)) = c r * ψ (j κ)
    rw [map_mul, hlaw _ _ hrS, (hSide.val _ hr).1]
    rw [show (j r).1 = kap π d r from rfl, bdet_kap]
  · intro κ hκ
    obtain ⟨p, hp, u, hu, hκe, -⟩ := hsupp (j κ) hκ
    obtain ⟨r, v, hr, hv, rfl, hvN⟩ := hUmain κ p u hp hu hκe
    have hrS : (j r).1 ∈ stab 𝔸[k] ({i} : Set ι) := hr
    have hrP : (r : G) ∈ P := (hSide.mem _).2 ((kap_mem_stab_iff π d i r).1 hr)
    refine ⟨r, v, hrP, hv, rfl, ?_⟩
    have hl := hlaw (j r) (j v) hrS
    have hφv : ψ (j v) ≠ 0 := fun h => hκ (by
      show ψ (j (r * v)) = 0
      rw [map_mul, hl, h, mul_zero])
    obtain ⟨p', hp', u', hu', hve, hval⟩ := hsupp (j v) hφv
    have hpN : p' ∈ N₁ := by
      have := hvN u' hu'
      rwa [hve, mul_inv_cancel_right] at this
    have hb : ‖f p' - 1‖ ≤ 1 / 4 := hNf p' hp' hpN
    show ‖ψ (j v) - (‖ψ (j v)‖ : ℂ)‖ ≤ ‖ψ (j v)‖ / 4
    generalize ψ (j v) = a at hval
    have e : a - (‖a‖ : ℂ) = (f p' - 1) * (‖a‖ : ℂ) := by
      rw [sub_mul, one_mul]
      exact congrArg (· - (‖a‖ : ℂ)) hval
    rw [e, norm_mul, Complex.norm_real, norm_norm]
    nlinarith [norm_nonneg a]
  · intro s κ
    show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) ω s = globalZeta (fun t => Ψ₁ fun _ => t) ω s * ψ (j κ)
    have hfun : (fun t => Ψ (t • vec (kap π d κ) i)) = fun t => (Ψ₁ fun _ => t) * ψ (j κ) :=
      funext fun t => hfac t (j κ)
    rw [hfun]
    unfold globalZeta
    rw [← integral_mul_const]
    congr 1
    ext x
    ring
  · obtain ⟨z, hz1, hz2⟩ := hz
    exact ⟨z, by linarith, hz2⟩
  · exact hone

end GlobalTheory.CompanionTheory.EisTestK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntSmul
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.He2M1

theorem thetaC_smul {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) :
    thetaC (c • F) h = c * thetaC F h := by
  unfold thetaC
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem thetaCInt_smul : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}), thetaCInt w (c • F) ω t = c * thetaCInt w F ω t := by
  intro k _ _ ι _ _ w c F ω t
  unfold thetaCInt
  simp only [thetaC_smul, mul_assoc]
  exact integral_const_mul c _

end GlobalTheory.CompanionTheory.He2M1
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToIdeleMulSelf
section
set_option synthInstance.maxSize 1000

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RgEisAsm

open PositivityTheory.RgEis PositivityTheory.RgEis.TF
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem toIdele_mul_self {ω : HeckeCharacter k} (hω : ω * ω = 1) (x : IdeleGroup k) :
    ω.toIdele x * ω.toIdele x = 1 := by
  have h := congrArg (fun f : HeckeCharacter k => f (IdeleClassGroup.mk k x)) hω
  simpa [HeckeCharacter.toIdele_apply] using h

theorem tensor_eq (φ : 𝓢(ι → mixedSpace k, ℂ)) (g : (ι → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (x : ι → 𝔸[k]) :
    GJMatrix.schwartzBruhatTensorPi φ g x = rd φ (fun j => (x j).1) * g (fun j => (x j).2) := rfl

theorem norm_inv_units (a : (InfiniteAdeleRing k)ˣ) (ha : ∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1)
    (w : InfinitePlace k) : ‖((a⁻¹ : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) w‖ = 1 := by
  have h : (a : InfiniteAdeleRing k) w * ((a⁻¹ : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) w = 1 :=
    congrFun (Units.mul_inv a) w
  have h2 := congrArg norm h
  rw [norm_mul, ha w, one_mul, norm_one] at h2
  exact h2

theorem line_inv {ω : HeckeCharacter k} (hω : ω * ω = 1) (φ₁ : 𝓢(Unit → mixedSpace k, ℂ))
    (g₁ : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (hφ : ∀ a : (InfiniteAdeleRing k)ˣ, (∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) →
      rd φ₁ (fun _ => (a : InfiniteAdeleRing k)) = ω.toIdele (ofInfinite a))
    (hg : ∀ u ∈ finiteIntegralUnits k, g₁ (fun _ => (u : FiniteAdeleRing (𝓞 k) k)) =
      ω.toIdele (ofFinite u))
    (a : (InfiniteAdeleRing k)ˣ) (u : (FiniteAdeleRing (𝓞 k) k)ˣ)
    (ha : ∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) (hu : u ∈ finiteIntegralUnits k) :
    GJMatrix.schwartzBruhatTensorPi φ₁ g₁
        (fun _ => (((ofInfinite a * ofFinite u)⁻¹ : IdeleGroup k) : 𝔸[k])) =
      ω.toIdele (ofInfinite a * ofFinite u) := by
  have h1 : (((ofInfinite a * ofFinite u)⁻¹ : IdeleGroup k) : 𝔸[k]).1 =
      ((a⁻¹ : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) := by
    have : toInfinite k (ofInfinite a * ofFinite u)⁻¹ = a⁻¹ := by simp
    exact congrArg Units.val this
  have h2 : (((ofInfinite a * ofFinite u)⁻¹ : IdeleGroup k) : 𝔸[k]).2 =
      ((u⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) := by
    have : toFinite k (ofInfinite a * ofFinite u)⁻¹ = u⁻¹ := by simp
    exact congrArg Units.val this
  rw [tensor_eq]
  simp only [h1, h2]
  rw [hφ _ (norm_inv_units a ha), hg _ (inv_mem hu), ← Circle.coe_mul, ← map_mul, map_inv, map_inv,
    ← mul_inv, map_inv]
  have h3 := toIdele_mul_self hω (ofInfinite a * ofFinite u)
  rw [inv_eq_of_mul_eq_one_left h3]

theorem near_one_nhds (hCol : ColLaw) (hTop : InMTop) (i₀ : ι) (M₀ : ℕ) (hM : M₀ ≠ 0)
    (U : Set ((adStd k).kGL ι)) (hU : U ∈ 𝓝 (1 : (adStd k).kGL ι)) :
    U ∩ {u : (adStd k).kGL ι | InM M₀ ((col i₀ u.1 i₀).2 - 1) ∧
      ∀ w, ‖(col i₀ u.1 i₀).1 w - 1‖ < 1} ∈ 𝓝 (1 : (adStd k).kGL ι) := by
  obtain ⟨-, hc, h1, -⟩ := hCol k ι i₀
  have hcc : Continuous fun u : (adStd k).kGL ι => col i₀ u.1 i₀ :=
    (continuous_apply i₀).comp (hc.comp continuous_subtype_val)
  refine inter_mem hU (IsOpen.mem_nhds ?_ ?_)
  · have o1 : IsOpen {u : (adStd k).kGL ι | InM M₀ ((col i₀ u.1 i₀).2 - 1)} :=
      ((hTop k).1 M₀ hM).1.preimage ((continuous_snd.comp hcc).sub continuous_const)
    have o2 : IsOpen {u : (adStd k).kGL ι | ∀ w, ‖(col i₀ u.1 i₀).1 w - 1‖ < 1} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_lt
        ((((continuous_apply w).comp (continuous_fst.comp hcc)).sub continuous_const).norm)
        continuous_const
    exact o1.inter o2
  · have e : col i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k]) i₀ = 1 := by
      have : col (k := k) i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k]) = Pi.single i₀ 1 := h1
      rw [this]; simp
    refine ⟨?_, fun w => ?_⟩
    · rw [e]
      exact ⟨0, (OH k).zero_mem, by
        show (1 : FiniteAdeleRing (𝓞 k) k) - 1 = _
        simp⟩
    · rw [e]
      simp

theorem asm : ColLaw → InMTop → Supp → ArchFun → FinFun → ZSplit → ZInf → ZFinPos → ZFinLim →
    StdGood → TestFun := by
  intro hCol hTop hSupp hArch hFin hZS hZI hZP hZL hStd k _ _ ι _ _ i₀ ω hω U hU
  obtain ⟨M₀, hM₀, hfin⟩ := hFin k ω
  have hU' := near_one_nhds hCol hTop i₀ M₀ hM₀ U hU
  obtain ⟨M, δ, hM, hdvd, hδ, hS⟩ := hSupp k ι i₀ ((hStd k).kcpt ι) _ hU' M₀ hM₀
  obtain ⟨g, g₁, hg, hg₁, hg1, hg₁u, hg₁b, hg₁p, hgV⟩ := hfin M hM hdvd ι i₀
  obtain ⟨φ, φ₁, hφ1, hφ₁u, hφ₁p, hφV⟩ := hArch k ι i₀ ω hω δ hδ
  obtain ⟨hcolK, hcc, hcol1, hcolP⟩ := hCol k ι i₀
  have hΨ := GJMatrix.schwartzBruhatTensorPi_mem φ hg
  have hΨ₁ := GJMatrix.schwartzBruhatTensorPi_mem φ₁ hg₁
  have hfac : ∀ (t : 𝔸[k]) (κ : (adStd k).kGL ι),
      GJMatrix.schwartzBruhatTensorPi φ g (t • col i₀ κ.1) =
        GJMatrix.schwartzBruhatTensorPi φ₁ g₁ (fun _ => t) *
          GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) := by
    intro t κ
    obtain ⟨hu, hp⟩ := hcolK κ.1 κ.2
    have a1 := (hφV _ hu).1 t.1
    have a2 := (hgV _ hp).1 t.2
    rw [tensor_eq, tensor_eq, tensor_eq]
    have e1 : (fun j => ((t • col i₀ κ.1) j).1) = t.1 • (fun j => (col i₀ κ.1 j).1) := rfl
    have e2 : (fun j => ((t • col i₀ κ.1) j).2) = t.2 • (fun j => (col i₀ κ.1 j).2) := rfl
    rw [e1, e2, a1, a2]
    ring
  have hequiv : ∀ p κ : (adStd k).kGL ι, p.1 ∈ stab 𝔸[k] {i₀} →
      GJMatrix.schwartzBruhatTensorPi φ g (col i₀ (p * κ).1) =
        ω.toIdele (bdet {i₀} p.1) * GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) := by
    intro p κ hp
    obtain ⟨hc, a, u, hb, ha, hu⟩ := hcolP p.1 p.2 hp
    have e : col i₀ (p * κ).1 = (((bdet {i₀} p.1)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) • col i₀ κ.1 := hc κ.1
    rw [e, hfac, hb, line_inv hω φ₁ g₁ hφ₁u hg₁u a u ha hu]
  have hone : rd φ₁ (fun _ => (1 : InfiniteAdeleRing k)) ≠ 0 := by
    have h := hφ₁u 1 (fun w => by
      rw [Units.val_one]
      exact norm_one (α := w.Completion))
    rw [Units.val_one] at h
    rw [h]
    simp
  have hunit : ∀ x : ℝ, 1 < x → zInf φ₁ ω x ≠ 0 := hZI k φ₁ ω hφ₁p hone
  refine ⟨GJMatrix.schwartzBruhatTensorPi φ g, GJMatrix.schwartzBruhatTensorPi φ₁ g₁,
    fun κ => GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1), hΨ, hΨ₁,
    (GJMatrix.continuous_of_mem_schwartzBruhatPi hΨ).comp (hcc.comp continuous_subtype_val),
    ?_, fun t κ => hfac t κ, ?_, fun p κ hp => hequiv p κ hp, ?_, ?_⟩
  · have e : col (k := k) i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k]) = Pi.single i₀ 1 := hcol1
    show GJMatrix.schwartzBruhatTensorPi φ g (col i₀ ((1 : (adStd k).kGL ι) : GL ι 𝔸[k])) = 1
    rw [e, tensor_eq]
    have e1 : (fun j => ((Pi.single i₀ (1 : 𝔸[k]) : ι → 𝔸[k]) j).1) = Pi.single i₀ 1 := by
      funext j
      by_cases h : j = i₀
      · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]; rfl
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]; rfl
    have e2 : (fun j => ((Pi.single i₀ (1 : 𝔸[k]) : ι → 𝔸[k]) j).2) = Pi.single i₀ 1 := by
      funext j
      by_cases h : j = i₀
      · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]; rfl
      · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]; rfl
    rw [e1, e2, hφ1, hg1, one_mul]
  · intro κ hne
    have hne' : GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) ≠ 0 := hne
    rw [tensor_eq] at hne'
    obtain ⟨n1, n2⟩ := mul_ne_zero_iff.1 hne'
    obtain ⟨hu, hpr⟩ := hcolK κ.1 κ.2
    obtain ⟨p, hp, u, huU, hκ⟩ := hS κ (fun j hj => (hgV _ hpr).2.1 n2 j hj) ((hφV _ hu).2.1 n1)
    refine ⟨p, hp, u, huU.1, hκ, ?_⟩
    obtain ⟨hu', hpr'⟩ := hcolK u.1 u.2
    have hreal : ∃ r : ℝ, 0 ≤ r ∧ GJMatrix.schwartzBruhatTensorPi φ g (col i₀ u.1) = r := by
      obtain ⟨r, hr, e⟩ := (hφV _ hu').2.2 huU.2.2
      rcases (hgV _ hpr').2.2 huU.2.1 with h | h
      · exact ⟨0, le_rfl, by rw [tensor_eq, h]; simp⟩
      · exact ⟨r, hr, by rw [tensor_eq, e, h, mul_one]⟩
    obtain ⟨r, hr, e⟩ := hreal
    have h1 : GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) = ω.toIdele (bdet {i₀} p.1) * r := by
      rw [hκ, hequiv p u hp, e]
    show GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1) =
      ω.toIdele (bdet {i₀} p.1) * (‖GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1)‖ : ℂ)
    have h2 : ‖GJMatrix.schwartzBruhatTensorPi φ g (col i₀ κ.1)‖ = r := by
      rw [h1, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_of_nonneg hr]
    rw [h2, h1]
  · have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i₀⟩
    have hcard' : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
    obtain ⟨x, hx, hz⟩ := hZL k g₁ ω hg₁ hg₁b (fun u hu => by
      rw [hg₁u u hu, ← Circle.coe_mul, toIdele_mul_self hω, Circle.coe_one]) ((Fintype.card ι : ℝ) + 1)
    refine ⟨x, by simpa using hx, ?_⟩
    rw [hZS k φ₁ g₁ ω x hg₁]
    exact mul_ne_zero (hunit x (by linarith)) hz
  · rintro rfl x hx
    rw [hZS k φ₁ g₁ 1 x hg₁]
    refine mul_ne_zero (hunit x hx) (hZP k g₁ hg₁ (hg₁p rfl) ?_ x hx)
    have h := hg₁u 1 (one_mem _)
    rw [Units.val_one] at h
    rw [h]
    simp

end GlobalTheory.CompanionTheory.RgEisAsm
end
end

