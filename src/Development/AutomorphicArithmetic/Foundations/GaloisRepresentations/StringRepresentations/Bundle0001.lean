import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.CuspAOfAb
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open GlobalTheory GlobalTheory.WeilDeligne UpperTheory.Lit.Car

namespace UpperTheory.GalN

theorem Aw.dim {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x y : WD h} (k : Aw x y) :
    x.lpDim = y.lpDim := by rw [← WD.charPol_natDegree x 1, k.pol, WD.charPol_natDegree]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem spl_iff (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} (c : G H.E N.Om → ℂ) (t : ℕ) (y : A.LP w) :
    Spl N A c t y ↔ SplW c t (T.e w y) := by
  constructor
  · rintro ⟨a, b, e, d, m, p⟩
    exact ⟨T.e w a, T.e w b, by rw [e, T.sum], by rw [T.dim, d], (T.mono0 w b).1 m,
      fun σ hσ => by rw [← T.inePol w b σ hσ, p σ hσ]⟩
  · rintro ⟨a, b, e, d, m, p⟩
    obtain ⟨a, rfl⟩ := (T.e w).surjective a
    obtain ⟨b, rfl⟩ := (T.e w).surjective b
    exact ⟨a, b, (T.e w).injective (by rw [e, T.sum]), by rw [← T.dim, d], (T.mono0 w b).2 m,
      fun σ hσ => by rw [T.inePol w b σ hσ, p σ hσ]⟩

theorem relW_of_aw (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h : Aw (T.e w x) (T.e w y)) : RelW N A x y := by
  refine ⟨by rw [← T.dim, ← T.dim, h.dim], fun σ hσ => ?_, fun m => (T.e w).injective (h.n0 ((T.mono0 w y).1 m)),
    fun u c t γ hγ hm hs => ?_⟩
  · rw [T.inePol _ _ σ hσ, T.inePol _ _ σ hσ, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, h.pol]
  · rw [spl_iff T, T.sum] at hs ⊢
    rw [T.inePol _ _ γ hγ, T.sum] at hm
    exact h.spl _ c t γ hγ hm hs

theorem relA_of_ab (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h : Ab (T.e w x) (T.e w y)) : RelA N A x y := by
  refine ⟨by rw [← T.dim, ← T.dim, h.dim], by rw [T.mono0, T.mono0]; exact h.mono, fun hy σ hσ => ?_⟩
  rw [T.inePol _ _ σ hσ, T.inePol _ _ σ hσ]
  rw [WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ]
  refine h.ine ((T.mono0 _ _).1 hy.1) (fun g hg => ?_) _ (deg_ineIncl _)
  have e := hy.2 g hg
  rw [T.inePol _ _ _ (comm_le_ine w hg), WD.inePol_of_mem _ g.2, ← T.dim] at e
  exact e

theorem cuspA_of_ab (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h1 : A.lpDim y ≠ 1)
    (h : Ab (T.e w x) (T.e w y)) : CuspA N A x y := ⟨relA_of_ab T h, fun e => absurd e h1⟩

end UpperTheory.GalN
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.ScalarOfCharpoly
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne

namespace UpperTheory.GalN

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem scalar_of_charpoly {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {f : End ℂ V}
    (hf : f.IsSemisimple) {c : ℂ} {t : ℕ} (e : f.charpoly = (X - C c) ^ t) (v : V) : f v = c • v := by
  have h1 : IsNilpotent (f - algebraMap ℂ (End ℂ V) c) := ⟨t, by
    have := LinearMap.aeval_self_charpoly f
    rw [e] at this
    simpa using this⟩
  have h2 : (f - algebraMap ℂ (End ℂ V) c).IsSemisimple := End.isSemisimple_sub_algebraMap_iff.2 hf
  have h3 := sub_eq_zero.1 (End.eq_zero_of_isNilpotent_isSemisimple h1 h2)
  rw [h3]; rfl

theorem exists_sum {W Va Vb : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [AddCommGroup Va] [Module ℂ Va] [FiniteDimensional ℂ Va] [AddCommGroup Vb] [Module ℂ Vb] [FiniteDimensional ℂ Vb]
    (x : WDRep h W) (a : WDRep h Va) (b : WDRep h Vb) (g : W ≃ₗ[ℂ] Va × Vb)
    (hg : ∀ σ v, g (x.ρ σ v) = (a.sum b).ρ σ (g v)) (hb : b.N = 0) (γ : Weil h) (hγ : deg γ = 0) (c : ℂ)
    (hbγ : ∀ v, b.ρ γ v = c • v) (haγ : ∀ v, a.ρ γ v = c • v → v = 0) (h0 : ∀ v, x.N (g.symm (0, v)) = 0) :
    ∃ a' : WDRep h Va, WD.mk x = WD.mk (a'.sum b) := by
  let M : End ℂ (Va × Vb) := g.conj x.N
  have hM : ∀ v, M (g v) = g (x.N v) := fun v => by simp [M, LinearEquiv.conj_apply]
  have hc : ∀ σ z, (a.sum b).ρ σ (M z) = ((normV w : ℕ) : ℂ) ^ deg σ • M ((a.sum b).ρ σ z) := fun σ z => by
    obtain ⟨v, rfl⟩ := g.surjective z
    have := LinearMap.congr_fun (x.comm σ) v
    simp only [End.mul_apply, LinearMap.smul_apply] at this
    rw [hM, ← hg, ← hg, hM, this, map_smul]
  have hs : Function.Surjective (a.ρ γ - c • (1 : End ℂ Va)) := by
    rw [← LinearMap.injective_iff_surjective, injective_iff_map_eq_zero]
    intro v hv
    exact haγ v (by simpa [sub_eq_zero] using hv)
  have h1 : ∀ v, M (0, v) = 0 := fun v => by
    rw [← g.apply_symm_apply (0, v), hM, h0, map_zero]
  have h2 : ∀ v, (M (v, 0)).2 = 0 := fun v => by
    obtain ⟨u, rfl⟩ := hs v
    have e : (((a.ρ γ - c • (1 : End ℂ Va)) u, 0) : Va × Vb) = (a.sum b).ρ γ (u, 0) - c • (u, 0) := by simp
    have k := hc γ (u, 0)
    rw [hγ, zpow_zero, one_smul] at k
    rw [e, map_sub, map_smul, ← k]
    simp [hbγ]
  let Na : End ℂ Va := LinearMap.fst ℂ Va Vb ∘ₗ M ∘ₗ LinearMap.inl ℂ Va Vb
  have h3 : ∀ v, M (v, 0) = (Na v, 0) := fun v => Prod.ext rfl (h2 v)
  have h4 : ∀ (k : ℕ) v, (M ^ k) (v, 0) = ((Na ^ k) v, 0) := fun k => by
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, ih, h3]
  have h5 : ∀ (k : ℕ) v, (M ^ k) (g v) = g ((x.N ^ k) v) := fun k => by
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, ih, hM]
  refine ⟨{ ρ := a.ρ, N := Na, smooth := a.smooth, semisimple := a.semisimple, nilpotent := ?_, comm := fun σ => ?_ },
    WD.sound ⟨g, hg, fun v => ?_⟩⟩
  · obtain ⟨k, hk⟩ := x.nilpotent
    refine ⟨k, LinearMap.ext fun v => ?_⟩
    have := h4 k v
    rw [← g.apply_symm_apply (v, 0), h5, hk] at this
    simpa using (congrArg Prod.fst this).symm
  · refine LinearMap.ext fun v => ?_
    have k := hc σ (v, 0)
    have e : (a.sum b).ρ σ (v, 0) = (a.ρ σ v, 0) := by simp
    rw [e, h3, h3] at k
    simpa using congrArg Prod.fst k
  · rw [← hM]
    obtain ⟨p, q⟩ := g v
    have e : ((p, q) : Va × Vb) = (p, 0) + (0, q) := by simp
    conv_lhs => rw [e, map_add, h1, h3, add_zero]
    simp [hb]

theorem aw_of_eigen {x y : WD h} (hp : ∀ g : Weil h, x.charPol g = y.charPol g) (h0 : y.mono0 → x = y)
    (hi : ∀ (n : ℕ) (x' y' : WDRep h (Fin n → ℂ)), WD.mk x' = x → WD.mk y' = y →
      ∀ χ : ↥(Ine (F := E) A) → ℂ, (∀ v, (∀ s, y'.ρ (ineIncl h s) v = χ s • v) → y'.N v = 0) →
        ∀ v, (∀ s, x'.ρ (ineIncl h s) v = χ s • v) → x'.N v = 0) : Aw x y := by
  refine ⟨hp, h0, fun u c t γ hγ hm ⟨a, b, e, d, m, p⟩ => ?_⟩
  obtain ⟨n, x, rfl⟩ := x.exists_rep
  obtain ⟨n', y, rfl⟩ := y.exists_rep
  obtain rfl : n = n' := by
    have h1 := WD.charPol_natDegree (WD.mk x) 1
    rw [hp, WD.charPol_natDegree] at h1
    simpa using h1.symm
  obtain ⟨k, u, rfl⟩ := u.exists_rep
  obtain ⟨i, a, rfl⟩ := a.exists_rep
  obtain ⟨j, b, rfl⟩ := b.exists_rep
  obtain ⟨ε, hε⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n n x y fun σ => by simpa using hp σ
  rw [e, WD.inePol_of_mem_Ine _ hγ, WD.lpSum_mk, WD.charPol_mk] at hm
  rw [WD.lpSum_mk, WD.lpSum_mk, WD.mk_eq_mk] at e
  obtain ⟨f, f1, f2⟩ := e
  have hbN : b.N = 0 := (WD.monodromyZero_ofWeilDeligneRepClass_iff b).1 m
  have hbc : ∀ s : ↥(Ine (F := E) A), (b.ρ (ineIncl h s)).charpoly = (X - C (c s)) ^ t := fun s => by
    have := p s s.2
    rwa [WD.inePol_of_mem_Ine _ s.2, WD.charPol_mk] at this
  have hb : ∀ (s : ↥(Ine (F := E) A)) v, b.ρ (ineIncl h s) v = c s • v :=
    fun s => scalar_of_charpoly (b.semisimple _) (hbc s)
  have ha : ∀ v, a.ρ (ineIncl h ⟨γ, hγ⟩) v = c γ • v → v = 0 := fun v hv => by
    by_contra hv0
    have hev : End.HasEigenvalue (a.ρ (ineIncl h ⟨γ, hγ⟩)) (c γ) :=
      End.hasEigenvalue_of_hasEigenvector ⟨End.mem_eigenspace_iff.2 hv, hv0⟩
    have hr := (End.hasEigenvalue_iff_isRoot_charpoly _ _).1 hev
    have hne := (LinearMap.charpoly_monic (a.ρ (ineIncl h ⟨γ, hγ⟩))).ne_zero
    rw [WDRep.sum_ρ, LinearMap.charpoly_prodMap, hbc ⟨γ, hγ⟩,
      rootMultiplicity_mul (mul_ne_zero hne ((monic_X_sub_C _).pow _).ne_zero), rootMultiplicity_X_sub_C_pow] at hm
    have := (rootMultiplicity_pos hne).2 hr
    omega

  have hz : ∀ z, (y.sum u).ρ (ineIncl h ⟨γ, hγ⟩) z = c γ • z → (y.sum u).N z = 0 := fun z hz => by
    apply f.injective
    have k1 := f1 (ineIncl h ⟨γ, hγ⟩) z
    rw [hz, map_smul] at k1
    have k2 : (f z).1 = 0 := ha _ (congrArg Prod.fst k1).symm
    rw [f2, map_zero]
    exact Prod.ext (by simp [k2]) (by simp [hbN])
  have hy : ∀ v, (∀ s, y.ρ (ineIncl h s) v = c s • v) → y.N v = 0 := fun v hv =>
    congrArg Prod.fst (hz (v, 0) (Prod.ext (hv ⟨γ, hγ⟩) (by simp)))
  have hx := hi n x y rfl rfl (fun s => c s) hy
  let g := (ε.prodCongr (LinearEquiv.refl ℂ (Fin k → ℂ))).trans f
  have hg : ∀ σ v, g ((x.sum u).ρ σ v) = (a.sum b).ρ σ (g v) := fun σ v => by
    show f _ = (a.sum b).ρ σ (f _)
    rw [← f1]
    exact congrArg f (Prod.ext (hε σ v.1) rfl)
  obtain ⟨a', e'⟩ := exists_sum (x.sum u) a b g hg hbN (ineIncl h ⟨γ, hγ⟩) (deg_ineIncl _) (c γ) (hb ⟨γ, hγ⟩) ha fun v => by
    have q : ∀ s : ↥(Ine (F := E) A), (x.sum u).ρ (ineIncl h s) (g.symm (0, v)) = c s • g.symm (0, v) := fun s => by
      apply g.injective
      rw [hg, map_smul, g.apply_symm_apply]
      exact Prod.ext (by simp) (hb s v)
    refine Prod.ext (hx _ fun s => congrArg Prod.fst (q s)) ?_
    have q2 := congrArg Prod.snd (q ⟨γ, hγ⟩)
    have q3 := congrArg Prod.snd (hz (0, (g.symm (0, v)).2) (Prod.ext (by simp) q2))
    exact q3
  exact ⟨WD.mk a', WD.mk b, by rw [WD.lpSum_mk, WD.lpSum_mk, e'], d, m, p⟩

end UpperTheory.GalN
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.UnrRecOfHasSat
section
noncomputable section

namespace UpperTheory.GalN

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
  {HT : (E →+* Qbar l) → Multiset ℤ} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

omit [IsCMField E] in
theorem Aw.eq_unr {h : IsPlaceOver A w} {x y : WD h} (k : Aw x y) (hy : y.unr) : x = y := k.n0 (WD.unr_mono0 _ hy)

omit [IsCMField E] in

theorem unr_rec_of_hasSat {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ) (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).unr := by
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ S).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hS⟩)
  have e := ParLaws.rec_eq_diag hrc (σ := ParLaws.toRep σ) hα
  have e' : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := e
  rw [e', WD.unr_mk]
  exact WDRep.unr_diag _

end UpperTheory.GalN
end
end

