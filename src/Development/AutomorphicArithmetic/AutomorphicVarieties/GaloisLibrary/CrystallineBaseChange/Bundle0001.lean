import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBCwOfQuadBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br

def NormQuad : Prop :=
  GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ η : HChar F, IsNormChar E η → IsQuadCharOf E η

def SelfIso : Prop :=
  StrongMultOneReal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (η : HChar F),
    η ^ 2 = 1 → SelfTw π.HasSat η → IsoTwist π η

def WeakEx : Prop :=
  CyclicBaseChange → ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E]
    [Algebra F E], Module.finrank F E = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ π : TR.CuspSub F a,
      (∃ η : HChar F, IsNormChar E η ∧ SelfTw π.HasSat η) ∨ ∃ P : CuspSub E a, IsBC0 π P

def BcAtt0 : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      (π.IsRegAlg → (CG.mk P).IsRegAlg) ∧ (AttR ι r π → IsSSRep (r.comp (Bc.res F Ω E)) → AttC ι (r.comp (Bc.res F Ω E)) P)

def BcConj0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
    (n : ℕ) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (Bc.cPl w) B

def BcDual0 : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ), 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.Polarized χ → IsBC0 π P →
    ∃ χ' : HChar (maximalRealSubfield K), (∀ v v' : InfinitePlace (maximalRealSubfield K), χ'.locInf v (-1) = χ'.locInf v' (-1)) ∧
      GlobalTheory.ContraPair.DualIsConjBy P (compNorm K χ')

def PlaceOf : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i →
    (∀ x : F, i (algebraMap F _ x) = algebraMap K _ (algebraMap F K x)) →
    w.under (𝓞 F) = v ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ IsPlaceOver A w ∧
      PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i

def WdAway : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i →
    ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)),
    ∀ (x : WD h) (y : WD h'), IsWDOf ι r x → IsWDOf ι (r.comp (Bc.res F Ω K)) y → WDRel (RingEquiv.refl Ω) x y

def RecInv : Prop :=
  GlobalTheory.Published.LocalLanglandsGL → ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K),
    PlaceIso A v A w (RingEquiv.refl Ω) j i → ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (v.adicCompletion F)))
    (σ' : SmIrr (GL (Fin n) (w.adicCompletion K))) rc rc', IsRec h rc → IsRec h' rc' →
    WDRel (RingEquiv.refl Ω) (rc (algNorm σ)) (rc' (algNorm σ')) →
    ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)

def SplitOf : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ExC → ExR →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.IsRegAlg → π.Polarized χ →
      IsBC0 π P → SplitIso π P

end UpperTheory.V.Br
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharConj
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open GlobalTheory.CuspRep (Af finId pFin)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)

section

variable {F : Type} [Field F] [NumberField F]

private theorem cc_finId_local (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)) = localIdele F w x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    simp
  · change (1 : Af F) - 1 + _ = _
    rw [sub_self, zero_add]
    rfl

private theorem cc_pFin_inf (v : InfinitePlace F) (x : (v.Completion)ˣ) :
    Units.map (pFin F).toMonoidHom (infIdele F v x) = 1 := Units.ext rfl

private theorem cc_split (k : Fˣ) :
    infDiag k * finId F (Units.map (algebraMap F (Af F)).toMonoidHom k) = diagUnits F k := by
  classical
  have h : ((infDiag k : Ideles F) : AdeleRing (𝓞 F) F) = (algebraMap F (InfiniteAdeleRing F) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace F, w.Completion) →* AdeleRing (𝓞 F) F :=
      MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    change ∏ w : InfinitePlace F, ι (Pi.mulSingle w (algebraMap F w.Completion k)) =
      ι (fun w => algebraMap F w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  refine Prod.ext ?_ ?_
  · change algebraMap F (InfiniteAdeleRing F) k * (1 - 0 + 0) = algebraMap F (InfiniteAdeleRing F) k
    simp
  · change (1 : Af F) * (1 - 1 + algebraMap F (Af F) k) = algebraMap F (Af F) k
    simp

private theorem cc_inf_fixed (hF : Module.finrank ℚ F = 1) (χ : HChar F) (a : (F →+* ℂ) → ℤ) (h : IsAlgPos χ a)
    (σ : ℂ ≃+* ℂ) (k : Fˣ) : σ ((χ.inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
  have hs : Function.Surjective (algebraMap ℚ F) := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hF).2
  obtain ⟨q, hq⟩ := hs (k : F)
  have h1 := h (k ^ 2) fun φ => by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_two_pos_of_ne_zero ((map_ne_zero φ).2 k.ne_zero)
  have h2 : ((χ.inf k : ℂˣ) : ℂ) ^ 2 = (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) ^ 2 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun φ _ => ?_
    rw [Units.val_pow_eq_pow_val, map_pow, ← hq, eq_ratCast, map_ratCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, mul_comm]
  have h3 : σ (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) = ∏ φ : F →+* ℂ, (q : ℂ) ^ a φ := by
    simp only [map_prod, map_zpow₀, map_ratCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with e | e
  · rw [e, h3]
  · rw [e, map_neg, h3]

end

theorem UpperTheory.V.Br.charConj :
    UpperTheory.V.Br.CharConj := by
  intro F _ _ hF χ a ha σ
  have hσ : ∀ k : Fˣ, σ ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) =
      ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) := fun k => by
    have h1 := χ.2.2 k
    rw [← cc_split k, map_mul] at h1
    have h2 : χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) = (χ.inf k)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    rw [h2, Units.val_inv_eq_inv_val, map_inv₀, cc_inf_fixed hF χ a ha σ k]
  let ψ : (Af F)ˣ →* ℂˣ := χ.1.comp (finId F)
  have hψ : Continuous ψ := χ.2.1.comp (GlobalTheory.CuspRep.continuous_finId F)
  let ψ' : (Af F)ˣ →* ℂˣ := (Units.map (σ : ℂ →+* ℂ).toMonoidHom).comp ψ
  have hψ' : Continuous ψ' := by
    refine continuous_of_continuousAt_one ψ' ?_
    have h1 : {u | ψ u = 1} ∈ nhds (1 : (Af F)ˣ) :=
      (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (map_one ψ)
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [h1] with u hu
    change 1 = Units.map _ (ψ u)
    rw [hu, map_one]
  let p := Units.map (pFin F).toMonoidHom
  have hp : Continuous p := Continuous.units_map _ continuous_snd
  let χ' : HChar F := ⟨χ.1 * (ψ.comp p)⁻¹ * ψ'.comp p, (χ.2.1.mul (hψ.comp hp).inv).mul (hψ'.comp hp), fun k => by
    have e : ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = ψ (Units.map (algebraMap F (Af F)).toMonoidHom k) :=
      Units.ext (hσ k)
    change χ.1 _ * (ψ (Units.map (algebraMap F (Af F)).toMonoidHom k))⁻¹ *
      ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = 1
    rw [χ.2.2 k, e, one_mul, inv_mul_cancel]⟩
  have hloc : ∀ w x, χ'.loc w x = Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.loc w x) := fun w x => by
    have e := cc_finId_local w x
    change χ.1 (localIdele F w x) * (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x))))⁻¹ *
      Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)))) = _
    rw [e, mul_inv_cancel, one_mul]
    rfl
  refine ⟨χ', fun v => ?_, fun w hw => ⟨fun x hx => ?_, ?_⟩⟩
  · change χ.1 (infIdele F v (-1)) * (ψ (Units.map (pFin F).toMonoidHom (infIdele F v (-1))))⁻¹ *
      ψ' (Units.map (pFin F).toMonoidHom (infIdele F v (-1))) = χ.1 (infIdele F v (-1))
    rw [cc_pFin_inf, map_one, map_one, inv_one, mul_one, mul_one]
  · rw [hloc, hw x hx, map_one]
  · exact congrArg Units.val (hloc w (atFin w (unif w)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ExistsPrimeNotMem
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp

open UpperTheory.V.Af

namespace UpperTheory.V.Br

private theorem inv_mem_eig {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (x : WD h) (φ : Weil h) {b : ℂ}
    (hb : (x.charPol φ⁻¹).IsRoot b) : b ≠ 0 ∧ b⁻¹ ∈ x.eig φ := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.charPol_mk, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hb
  obtain ⟨v, hv⟩ := hb.exists_hasEigenvector
  have h1 : v = b • a.ρ φ v := by
    rw [← map_smul, ← hv.apply_eq_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hv.2 (by simpa using h1)
  refine ⟨hb0, ?_⟩
  rw [WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨Module.End.mem_eigenspace_iff.2 ?_, hv.2⟩
  conv_rhs => rw [h1]
  rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]

private theorem norm_of_pure {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {B : Multiset ℂ} (hB : FrobEig ι r w B) {x : WD h} (hx : IsWDOf ι r x) {s : ℝ} (ht : (x.lpTw s).tempered) :
    ∀ b ∈ B, ‖b‖ = (normV w : ℝ) ^ s := by
  intro b hb
  obtain ⟨hu, hf⟩ := hB A h
  have e := hx.wdOf_eq hl
  obtain ⟨t, ht', φ, hφ, N, a, hN, -, -⟩ := id hx
  have hxu : x.unr := e ▸ (hN.unr_wdOf_iff hl ht' ι).2 hu
  have hc := hN.charPol_wdOf (h := h) hl ht' ι (frob h)⁻¹
  rw [e] at hc
  have hr : (x.charPol (frob h)⁻¹).IsRoot b := by
    rw [hc]
    erw [hf _ isFrob_frob]
    have := (mem_roots (Polynomial.monic_multiset_prod_of_monic B (fun b => X - C b)
      fun b _ => monic_X_sub_C b).ne_zero).1 ((roots_multiset_prod_X_sub_C B).symm ▸ hb)
    exact this
  obtain ⟨hb0, hm⟩ := inv_mem_eig x _ hr
  have h1 := (WD.tempered_unr _ ((WD.unr_tw x s).2 hxu)).1 ht (b⁻¹ * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (by
    rw [WD.frobEig_tw x s hxu]
    exact Multiset.mem_map_of_mem _ hm)
  rw [norm_mul, norm_inv, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (GlobalTheory.WeilDeligne.one_lt_normV w)), Complex.ofReal_re,
    inv_mul_eq_one₀ (norm_ne_zero_iff.2 hb0)] at h1
  exact h1

private theorem wt_eq {n : ℕ} (hn : 1 ≤ n) {m : Fin n → ℤ} {wt wt' : ℤ} (hm : ∀ i, m i + m i.rev = wt) {H : Multiset ℤ}
    (h1 : H.map (fun n : ℤ => (n : ℂ)) = (infOf m).map fun z => ((n : ℂ) - 1) / 2 - z) (h2 : H = H.map (wt' - ·)) :
    wt' = -wt := by
  have e : H = Finset.univ.val.map fun i => -m i := by
    refine Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_
    rw [h1, infOf, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp
  have s1 := congrArg Multiset.sum h2
  rw [e, Multiset.map_map] at s1
  change ∑ i, -m i = ∑ i, (wt' - -m i) at s1
  have s2 : ∑ i : Fin n, (m i + m i.rev) = ∑ _i : Fin n, wt := Finset.sum_congr rfl fun i _ => hm i
  have s3 : ∑ i : Fin n, m i.rev = ∑ i, m i := Equiv.sum_comp Fin.revPerm m
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, s3] at s1 s2
  have hn' : (n : ℤ) ≠ 0 := by omega
  refine mul_left_cancel₀ hn' ?_
  linarith

private theorem exists_prime_not_mem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ∃ l : ℕ, l.Prime ∧ ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  by_contra H
  push_neg at H
  have h2 := H 2 Nat.prime_two
  have h3 := H 3 Nat.prime_three
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  have := w.asIdeal.sub_mem h3 h2
  norm_num at this
  exact this

end UpperTheory.V.Br

theorem UpperTheory.V.Br.pureP :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.PureP := by
  intro P K _ _ _ n hn m wt hm hwt M π hπ w B hB
  obtain ⟨hinf, ⟨χ, hχ⟩, -⟩ := hπ
  obtain ⟨l, hlp, hl⟩ := UpperTheory.V.Br.exists_prime_not_mem w
  haveI : Fact l.Prime := ⟨hlp⟩
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  have hic : ∀ τ, (CG.mk π).infChar τ = UpperTheory.V.Af.infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  obtain ⟨r, wt', HT, hr⟩ := P.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π χ hreg hχ
  have hHT : ∀ τ, (HT τ).map (fun n : ℤ => (n : ℂ)) = (UpperTheory.V.Af.infOf m).map fun z => ((n : ℂ) - 1) / 2 - z := fun τ => by
    rw [hr.weights τ, hic]
  obtain ⟨τ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  have e : wt' = -wt := by
    refine UpperTheory.V.Br.wt_eq (by omega) hwt (hHT (ι.symm.toRingHom.comp τ₀)) ?_
    rw [← hr.weights_conj]
    exact Multiset.map_injective (Int.cast_injective (α := ℂ)) ((hHT _).trans (hHT _).symm)
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := UpperTheory.V.Af.locCompC P K n π w
  have hs := ((UpperTheory.V.Af.satLoc P K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  have hF := UpperTheory.V.Af.satFrob P K (AlgebraicClosure K) l ι n r hr.cont w hl σ B hs
    fun A h rc hrc => hr.away w hl A h rc hrc σ hσ
  obtain ⟨A, hA⟩ := exists_isPlaceOver (AlgebraicClosure K) w
  obtain ⟨x, hx, ht⟩ := hr.pure w hl A hA
  have := UpperTheory.V.Br.norm_of_pure hl hF hx ht
  rw [e] at this
  simpa using this
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FinCompR
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep GlobalTheory.CuspRep.LocEx
open GlobalTheory.CuspRep (SmIrr Af locGL pLoc finGL)

namespace UpperTheory.V.Br.FiniteLocalComponent

open UpperTheory.V UpperTheory.V.Af

section Gen

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]

private def orb (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x

private theorem orb_comm (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
    (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
  simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

private theorem orb_act (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
    orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' h h' => rw [Finsupp.mapDomain_add, map_add, map_add, map_add, h, h']
  | single a b => simp [orb]

private def annPart (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V where
  carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
  add_mem' := fun {x y} hx hy c hc => by
    have : orb κ (x + y) c = orb κ x c + orb κ y c := by
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add, smul_add, Finset.sum_add_distrib]
    rw [this, hx c hc, hy c hc, add_zero]
  zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
  smul_mem' := fun a x hx c hc => by
    have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
    simpa [hx c hc] using this

private theorem exists_type (κ : Representation ℂ K V) (φ : V)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
    ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
      (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
  have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨_, orb_act κ φ k c⟩
  haveI : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
    rw [orb, Finsupp.range_linearCombination]; exact hφ
  let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
  obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
  have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
    rw [← sub_eq_zero, ← map_sub]
    refine hx _ ?_
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
  refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
    ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
  · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
    obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
    have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
        b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
      have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
        Subtype.ext (orb_act κ φ k c)
      rw [h2]
      exact LinearMap.toMatrix_mulVec_repr b b _ _
    rw [h1]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
    simp [orb]

end Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem smooth_fin (π : TR.CuspSub F n) : IsSmooth π.finPart := fun v => by
  convert (π.cusp v.1 v.2).1.level using 1
  ext k
  exact Subtype.ext_iff

private theorem cpt_fin (π : TR.CuspSub F n) (k : TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (TR.rt F n (TR.infGL F n (Unitary.toUnits k)) * TR.rt F n (finGL F n g)) y.1 =
    (TR.rt F n (finGL F n g) * TR.rt F n (TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, TR.infGL_comm]

private theorem bot_or_top (π : TR.CuspSub F n) (W : Submodule ℂ π.V)
    (h1 : ∀ g, ∀ x ∈ W, π.finPart g x ∈ W)
    (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.finPart g x) = π.finPart g (T x)) → ∀ x ∈ W, T x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
    cases o with
    | fin k => exact h1 k x hx
    | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
    | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X g) y.1)) x hx
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h | h
  · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))

private def cptPart (π : TR.CuspSub F n) : Representation ℂ (TR.Kinf F n) π.V :=
  sub (TR.cptRep F n) π.V fun k => π.stable (.cpt k)

private theorem exists_comp (h : UpperTheory.V.Published.AdmissibleReal) (π : TR.CuspSub F n) :
    ∃ τ, π.IsFinComp τ := by
  obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ : π.V := ⟨φ₀, hφ⟩
  have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  set L := stab π.finPart φ
  have hL : IsOpen (L : Set (GL (Fin n) (Af F))) := smooth_fin π _
  obtain ⟨K₀, ho₀, hc₀⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact F n
  have ho : IsOpen ((K₀ ⊓ L : Subgroup _) : Set (GL (Fin n) (Af F))) := ho₀.inter hL
  have hc : IsCompact ((K₀ ⊓ L : Subgroup _) : Set (GL (Fin n) (Af F))) :=
    hc₀.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
    have := (π.cusp φ₀ hφ).1.kfin
    refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
      (Submodule.span ℂ (Set.range fun k => TR.cptRep F n k φ₀)) fun v => ?_)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
  have hcomm : ∀ g k x, π.finPart g (cptPart π k x) = cptPart π k (π.finPart g x) := fun g k x => (cpt_fin π k g x).symm
  obtain ⟨σ, hσ, -⟩ := exists_irred (smooth_fin π) ho (fun W hW e => by
      rcases bot_or_top π (nullPart π.finPart (K₀ ⊓ L)) (fun g x hx => nullPart_act _ _ g hx)
        (fun T hT x hx => nullPart_comm _ _ T hT hx) with h2 | h2
      · exact le_bot_iff.1 (h2 ▸ le_nullPart (smooth_fin π) hc W hW e)
      · exact absurd (eq_zero_of_mem_nullPart (smooth_fin π) hc (mem_fix.2 fun k hk => hk.2)
          (h2 ▸ Submodule.mem_top)) h0')
    (annPart (cptPart π) φ) (fun g x hx c hc => by rw [orb_comm _ _ (hcomm _), hx c hc, map_zero])
    ((Submodule.ne_bot_iff _).2 ⟨φ, fun _ hc => hc, h0'⟩) (fun K' hK' => by
      obtain ⟨W, hW, hWf⟩ := h F n π K' hK' d ξ
      refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
      obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1
      refine hWf f hf (fun k hk v => ?_) hx1
      obtain ⟨c, hc⟩ := hf2 v
      rw [hc, ← orb_comm _ _ (hcomm k), mem_fix.1 hx.2 k hk])
  exact ⟨σ, hσ⟩

end UpperTheory.V.Br.FiniteLocalComponent

theorem UpperTheory.V.Br.finCompR :
    UpperTheory.V.Published.AdmissibleReal → UpperTheory.V.Br.FinCompR := fun h _ _ _ _ _ π =>
  UpperTheory.V.Br.FiniteLocalComponent.exists_comp h π
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.KlevThree
section
private theorem klev_three (K : Type) [Field K] [NumberField K] (n M : ℕ) :
    UpperTheory.V.Af.KLev K n (3 * M) ≤ UpperTheory.V.Af.KLev K n M := by
  refine Subgroup.map_mono fun k hk => ?_
  have hle : Ideal.span {((3 * M : ℕ) : ↥(UpperTheory.V.Af.Ohat K))} ≤ Ideal.span {(M : ↥(UpperTheory.V.Af.Ohat K))} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (Dvd.intro_left 3 rfl))
  have e := congrArg (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.factor hle)) (MonoidHom.mem_ker.1 hk)
  rw [map_one] at e
  exact e

theorem UpperTheory.V.Br.cardP :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.CardP := by
  intro P K _ _ _ n hn
  obtain ⟨c₁, A₁, hW⟩ := UpperTheory.V.Af.weylC P K n
  obtain ⟨c₂, A₂, hC⟩ := UpperTheory.V.Af.cohBoundFree K (Or.inl inferInstance) n ⊤ inferInstance
  refine ⟨c₂ * c₁, A₁ + A₂, fun m hm H hH M hM S hS hiso => ?_⟩
  obtain ⟨Ξ, hΞ, hd⟩ := hW m hm H hH
  have h3 : 1 ≤ 3 * M := by omega
  have hB := P.borelC K n (by omega) (UpperTheory.V.Af.KLev K n (3 * M)) (by apply UpperTheory.V.Af.isOpen_KLev; exact h3)
    (by apply UpperTheory.V.Af.isCompact_KLev; exact h3) Ξ S hiso fun π hπ =>
      ⟨P.cohC K n (by omega) π Ξ fun τ => ⟨_, (hS π hπ).1 τ, hΞ τ⟩,
        (hS π hπ).2.2.imp fun _ hv => ⟨hv.1, fun u hu => hv.2 u (klev_three K n M hu)⟩⟩
  have h1 : S.card ≤ c₂ * M ^ A₂ * Ξ.d := Nat.cast_le.1 (hB.trans (hC M hM _ _))
  have h2 : M ^ A₂ ≤ M ^ (A₁ + A₂) := Nat.pow_le_pow_right hM (by omega)
  have h4 : (H + 1) ^ A₁ ≤ (H + 1) ^ (A₁ + A₂) := Nat.pow_le_pow_right (by omega) (by omega)
  calc S.card ≤ c₂ * M ^ A₂ * Ξ.d := h1
    _ ≤ c₂ * M ^ (A₁ + A₂) * (c₁ * (H + 1) ^ (A₁ + A₂)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) (hd.trans (Nat.mul_le_mul_left _ h4))
    _ = c₂ * c₁ * (M * (H + 1)) ^ (A₁ + A₂) := by rw [mul_pow]; ring
end

