import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.ConjIsoOf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC

theorem conjIso_of (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (smo : StrongMultOneReal) (h7 : SSmo) (h8 : SConjSpaceC) (h9 : SConjSpaceR)
    (h10 : SConjSatC) (h11 : SConjSatR) {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {n : ℕ} (hn : 1 ≤ n) (P : Cusp M n) (σ : M ≃ₐ[K] M)
    (H : ∀ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g →
      (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) → (∀ w, normV (g w) = normV w) →
      ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∃ B, P.sat w B ∧ P.sat (g w) B) :
    P.ConjIso σ.toRingEquiv := by
  intro s hs
  have key : ∃ P' : Cusp M n,
      P'.space = (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' P.space ∧
      ∃ g : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 M), Function.Injective g ∧ (∀ w, (g w).under (𝓞 K) = w.under (𝓞 K)) ∧
        (∀ w, normV (g w) = normV w) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ B, P.sat (g w) B → P'.sat w B := by
    cases P with
    | cx P =>
      obtain ⟨P', hP'⟩ := h8 M σ.toRingEquiv s hs n P
      exact ⟨.cx P', hP', h10 K M σ s hs n P P' hP'⟩
    | re P =>
      obtain ⟨P', hP'⟩ := h9 M σ.toRingEquiv s hs n P
      exact ⟨.re P', hP', h11 K M σ s hs n P P' hP'⟩
  obtain ⟨P', hsp, g, hinj, hund, hnorm, hsat⟩ := key
  refine ⟨P', hsp, h7 hN smo M n hn P' P ?_⟩
  filter_upwards [hsat, H g hinj hund hnorm] with w hB ⟨B, hB1, hB2⟩
  exact ⟨B, hB _ hB2, hB1⟩

theorem top (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (smo : StrongMultOneReal) (h1 : SCuspOf) (h2 : SIsCusp) (h3 : SIsoSat) (h4 : STwSat)
    (h5 : SSatEx) (h6 : SSatUniq) (h7 : SSmo) (h8 : SConjSpaceC) (h9 : SConjSpaceR) (h10 : SConjSatC) (h11 : SConjSatR)
    (h12 : SNormPow) : LitCBC → CyclicBaseChange := by
  intro L K M _ _ _ _ _ _ hp hK hM n hn
  obtain ⟨L1, L2, L3⟩ := L K M hp hK hM n hn
  refine ⟨?_, ?_, ?_⟩
  · intro sat inf hc
    obtain ⟨π, rfl, rfl⟩ := h1 K n sat inf hc
    rcases L1 π with ⟨η, hη, hi⟩ | ⟨P, hw, hinf⟩
    · refine Or.inl ⟨η, hη, ?_⟩
      filter_upwards [h4 K n π η, h5 K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩
      exact ⟨hu, B, hB, h6 K n π v _ _ (h3 K n _ _ hi v _ (ht B hB)) hB⟩
    · exact Or.inr ⟨P.sat, P.inf, h2 M n P, hw, hinf⟩
  · intro sat' inf' hc' hinv
    obtain ⟨P, rfl, rfl⟩ := h1 M n sat' inf' hc'
    refine (fun ⟨π, hw, hinf⟩ => ⟨π.sat, π.inf, h2 K n π, hw, hinf⟩) (L2 P fun σ => ?_)
    refine conjIso_of hN smo h7 h8 h9 h10 h11 hn P σ fun g _ hund _ => ?_
    filter_upwards [hinv] with w hall
    exact hall (g w) (hund w)
  · intro sat inf sat' inf' hc hc' hw
    obtain ⟨π, rfl, rfl⟩ := h1 K n sat inf hc
    obtain ⟨P, rfl, rfl⟩ := h1 M n sat' inf' hc'
    have hconj : ∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv := fun σ => by
      refine conjIso_of hN smo h7 h8 h9 h10 h11 hn P σ fun g hinj hund hnorm => ?_
      filter_upwards [hw, hinj.tendsto_cofinite.eventually hw] with w h1' h2'
      obtain ⟨f, hf⟩ := h12 K M w
      obtain ⟨B, hB, hPB⟩ := h1' f hf
      obtain ⟨B', hB', hPB'⟩ := h2' f (by rw [hnorm w, hund w]; exact hf)
      rw [hund w] at hB'
      obtain rfl := h6 K n π _ _ _ hB hB'
      exact ⟨_, hPB, hPB'⟩
    obtain ⟨La, Lb⟩ := L3 π P hconj hw
    refine ⟨fun η hη ht => La η hη (h7 hN smo K n hn _ _ ?_), fun sat₁ inf₁ hc₁ hw₁ => ?_⟩
    · filter_upwards [ht, h4 K n π η] with v ⟨_, B, hB, he⟩ ⟨_, htw⟩
      exact ⟨B, he ▸ htw B hB, hB⟩
    · obtain ⟨π₁, rfl, rfl⟩ := h1 K n sat₁ inf₁ hc₁
      obtain ⟨η, hη, hi⟩ := Lb π₁ hw₁
      refine ⟨η, hη, ?_⟩
      filter_upwards [h4 K n π η, h5 K n π] with v ⟨hu, ht⟩ ⟨B, hB⟩
      exact ⟨hu, B, hB, h3 K n _ _ hi v _ (ht B hB)⟩

end UpperTheory.CBC
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PBasic
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.CBC.SCuspOf_holds : UpperTheory.CBC.SCuspOf := by
  intro F _ _ n sat inf h
  rcases h with ⟨hC, π, rfl, rfl⟩ | ⟨hR, π, rfl, rfl⟩
  · exact ⟨.cx π, rfl, rfl⟩
  · exact ⟨.re π, rfl, rfl⟩

theorem UpperTheory.CBC.SIsCusp_holds : UpperTheory.CBC.SIsCusp := by
  intro F _ _ n π
  cases π with
  | cx π => exact Or.inl ⟨inferInstance, π, rfl, rfl⟩
  | re π => exact Or.inr ⟨inferInstance, π, rfl, rfl⟩

theorem UpperTheory.CBC.SSatUniq_holds : UpperTheory.CBC.SSatUniq := by
  intro F _ _ n π v B B' h h'
  cases π with
  | cx π => exact CG.HasSat.unique (π := CG.mk π) (w := v) h h'
  | re π => exact UpperTheory.V.TR.CuspSub.HasSat.unique (π := π) (w := v) h h'
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSConjSatC
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep

namespace UpperTheory.CBC.SConjSatCAux

theorem hasSatGL_of_linEquiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hf : ∀ g y, T.toLinearMap (ρ g y) = ρ' g (T.toLinearMap y)) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w ρ' B := by
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    have h1 := hx.map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine (hB.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) fun e => h0 (by rw [e, map_zero])).map
      T.toLinearMap hf h0
    exact (hf k x).trans (GlobalTheory.LGrp.mem_fixed.1 hy k hk)

theorem conjSrc_conjSrc_symm {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc c (conjSrc c.symm w) = w := by
  refine (eq_conjSrc ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).2 ?_)).symm
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc c.symm w)]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  have e : (RingOfIntegers.mapRingEquiv c.symm) ((RingOfIntegers.mapRingEquiv c) x) = x := by
    ext
    simp
  rw [e]

variable {M : Type} [Field M] [NumberField M] [IsTotallyComplex M]

theorem pInf_s_sFin (s : Ad M ≃+* Ad M) (hs : Continuous s) (y : Af M) : pInf M (s (sFin M y)) = 0 := by
  let f : Af M →+ Cinf M :=
    { toFun := fun y => pInf M (s (sFin M y))
      map_zero' := by simp
      map_add' := fun a b => by simp [map_add] }
  have hf : Continuous f := by
    have h1 : Continuous fun y : Af M => (sFin M y : Ad M) :=
      (continuous_const.prodMk continuous_id : Continuous fun y : Af M => ((0 : InfiniteAdeleRing M), y))
    show Continuous fun y : Af M => pInf M (s (sFin M y))
    exact (GlobalTheory.CuspRep.ContAut.continuous_pInf (E := M)).comp (hs.comp h1)
  have hint : ∀ z ∈ GlobalTheory.SchADecomp.intA M, f z = 0 := by
    intro z hz
    funext τ
    obtain ⟨C, hC⟩ := (GlobalTheory.SchADecomp.isCompact_intA (F := M)).exists_bound_of_continuousOn
      ((continuous_apply τ).comp hf).continuousOn
    by_contra h0
    have hpos : 0 < ‖f z τ‖ := norm_pos_iff.2 h0
    obtain ⟨m, hm⟩ := exists_nat_gt (C / ‖f z τ‖)
    have h2 := hC (m • z) (AddSubgroup.nsmul_mem _ hz m)
    rw [Function.comp_apply, map_nsmul, Pi.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast] at h2
    rw [div_lt_iff₀ hpos] at hm
    linarith
  obtain ⟨N, hN, hNy⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact M (κ := Unit)
    (isCompact_singleton (x := fun _ : Unit => y))
  have hmem : (N : Af M) * y ∈ GlobalTheory.SchADecomp.intA M := fun v => hNy _ (Set.mem_singleton _) () v
  have h3 := hint _ hmem
  rw [← nsmul_eq_mul, map_nsmul] at h3
  show f y = 0
  funext τ
  have h4 := congrFun h3 τ
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h4
  exact (mul_eq_zero.1 h4).resolve_left (by exact_mod_cast hN.ne')

theorem s_sFin (σ : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : IsGalAd σ s) (y : Af M) :
    s (sFin M y) = sFin M (conjFin σ y) := by
  refine ad_ext ?_ ?_
  · rw [pInf_s_sFin s hs.1]
    exact (map_zero (infEq M).symm).symm
  · exact hs.2.2 _

theorem map_finGL (σ : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : IsGalAd σ s) {n : ℕ} (k : GL (Fin n) (Af M)) :
    Matrix.GeneralLinearGroup.map s.toRingHom (finGL M n k) =
      finGL M n (Matrix.GeneralLinearGroup.map (conjFin σ) k) := by
  ext i j
  change s ((1 : Matrix (Fin n) (Fin n) (Ad M)) i j - sFin M ((1 : Matrix (Fin n) (Fin n) (Af M)) i j) +
      sFin M (k.1 i j)) = (1 : Matrix (Fin n) (Fin n) (Ad M)) i j -
      sFin M ((1 : Matrix (Fin n) (Fin n) (Af M)) i j) + sFin M (conjFin σ (k.1 i j))
  have e1 : s ((1 : Matrix (Fin n) (Fin n) (Ad M)) i j) = (1 : Matrix (Fin n) (Fin n) (Ad M)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have e2 : conjFin σ ((1 : Matrix (Fin n) (Fin n) (Af M)) i j) = (1 : Matrix (Fin n) (Fin n) (Af M)) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [map_add, map_sub, e1, s_sFin σ s hs, s_sFin σ s hs, e2]

theorem main (σ : M ≃+* M) (s : Ad M ≃+* Ad M) (hs : IsGalAd σ s) {n : ℕ} (P P' : CuspSub M n)
    (hsp : (Cusp.cx P').space =
      (fun f : GA M n → ℂ => fun g => f (Matrix.GeneralLinearGroup.map s.toRingHom g)) '' (Cusp.cx P).space)
    (v : HeightOneSpectrum (𝓞 M)) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL v (P.locRep v) B) :
    GlobalTheory.LFun.HasSatGL (conjSrc σ v) (P'.locRep (conjSrc σ v)) B := by
  set S : GA M n →* GA M n := Matrix.GeneralLinearGroup.map s.toRingHom with hS
  have hSs : ∀ g, S (Matrix.GeneralLinearGroup.map s.symm.toRingHom g) = g := fun g => by
    ext i j
    exact s.apply_symm_apply _
  have hfwd : ∀ φ : Sm M n, φ ∈ P.V → ∃ ψ : Sm M n, ψ ∈ P'.V ∧ (fun g => φ.1 (S g)) = ψ.1 := fun φ hφ => by
    have h : (fun g => φ.1 (S g)) ∈ (Cusp.cx P').space := hsp ▸ ⟨φ.1, ⟨φ, hφ, rfl⟩, rfl⟩
    obtain ⟨ψ, hψ, e⟩ := h
    exact ⟨ψ, hψ, e⟩
  have hbwd : ∀ ψ : Sm M n, ψ ∈ P'.V → ∃ φ : Sm M n, φ ∈ P.V ∧ ψ.1 = fun g => φ.1 (S g) := fun ψ hψ => by
    have h : ψ.1 ∈ (Cusp.cx P').space := ⟨ψ, hψ, rfl⟩
    rw [hsp] at h
    obtain ⟨f, ⟨φ, hφ, rfl⟩, e⟩ := h
    exact ⟨φ, hφ, e.symm⟩
  have hT : ∀ φ : P.V, ∃ h : (fun g => φ.1.1 (S g)) ∈ Sm M n, (⟨_, h⟩ : Sm M n) ∈ P'.V := fun φ => by
    obtain ⟨ψ, hψ, e⟩ := hfwd φ.1 φ.2
    have h : (fun g => φ.1.1 (S g)) ∈ Sm M n := by rw [e]; exact ψ.2
    refine ⟨h, ?_⟩
    have e2 : (⟨_, h⟩ : Sm M n) = ψ := Subtype.ext e
    rw [e2]
    exact hψ
  let T : P.V →ₗ[ℂ] P'.V :=
    { toFun := fun φ => ⟨⟨_, (hT φ).1⟩, (hT φ).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hTinj : Function.Injective T := fun φ φ' e => by
    have e1 : (fun g => φ.1.1 (S g)) = fun g => φ'.1.1 (S g) := congrArg (fun x : P'.V => x.1.1) e
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have := congrFun e1 (Matrix.GeneralLinearGroup.map s.symm.toRingHom g)
    simpa only [hSs] using this
  have hTsurj : Function.Surjective T := fun ψ => by
    obtain ⟨φ, hφ, e⟩ := hbwd ψ.1 ψ.2
    exact ⟨⟨φ, hφ⟩, Subtype.ext (Subtype.ext e.symm)⟩
  let TE : P.V ≃ₗ[ℂ] P'.V := LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩
  have hinter : ∀ (k : GL (Fin n) ((conjSrc σ v).adicCompletion M)) (y : P.V),
      T (P.locRep v (Matrix.GeneralLinearGroup.map (conjLoc σ v) k) y) = P'.locRep (conjSrc σ v) k (T y) := by
    intro k y
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq]
    change y.1.1 (S g * finGL M n (locGL M n v (Matrix.GeneralLinearGroup.map (conjLoc σ v) k))) =
      y.1.1 (S (g * finGL M n (locGL M n (conjSrc σ v) k)))
    rw [map_mul, hS, map_finGL σ s hs, GlobalTheory.ConjPairLoc.conjFin_locGL]
  let ψ : (conjSrc σ v).adicCompletion M ≃+* v.adicCompletion M :=
    RingEquiv.ofBijective (conjLoc σ v) ⟨(conjLoc σ v).injective, GlobalTheory.CuspRep.ParLaws.conjLoc_surjective σ v⟩
  let ψ₀ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv M v ≃+* (conjSrc σ v).adicCompletion M := ψ.symm
  have h3 : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv M v, Valued.v (ψ₀ a) = Valued.v a := fun a => by
    have := (conjLoc_spec σ v).2.2 (ψ₀ a)
    have e : conjLoc σ v (ψ₀ a) = a := ψ.apply_symm_apply a
    rw [e] at this
    exact this.symm
  have hq : Formalism.UG.qV M (conjSrc σ v) = Formalism.UG.qV M v := GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc σ v
  have hk : ∀ k, (GlobalTheory.LFun.SplitTie.glEquiv n ψ₀).symm k = Matrix.GeneralLinearGroup.map (conjLoc σ v) k :=
    fun k => by ext i j; rfl
  have hK := GlobalTheory.LFun.SplitTie.mem_KGL_iff (n := n) h3
  let ρ'' := (P.locRep v).comp (GlobalTheory.LFun.SplitTie.glEquiv n ψ₀).symm.toMonoidHom
  have hfix : ∀ x, x ∈ GlobalTheory.PRep.fixed ρ'' (GlobalTheory.LFun.KGL (conjSrc σ v) n) ↔
      x ∈ GlobalTheory.PRep.fixed (P.locRep v) (GlobalTheory.LFun.KGL v n) := fun x => GlobalTheory.LFun.mem_fixed_comp_symm _ hK
  have hB'' : GlobalTheory.LFun.HasSatGL (conjSrc σ v) ρ'' B := by
    refine ⟨?_, fun x hx h0 => (GlobalTheory.LFun.SplitTie.isSatVecGL_comp_symm h3 hq _ x B).2 (hB.2 x ((hfix x).1 hx) h0)⟩
    obtain ⟨x, hx⟩ := hB.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨x, (hfix x).2 hx.2.1, hx.1⟩
  refine hasSatGL_of_linEquiv TE (fun k y => ?_) hB''
  change T (P.locRep v ((GlobalTheory.LFun.SplitTie.glEquiv n ψ₀).symm k) y) = _
  rw [hk]
  exact hinter k y

end UpperTheory.CBC.SConjSatCAux

open UpperTheory.CBC in
theorem UpperTheory.CBC.SConjSatC_holds : UpperTheory.CBC.SConjSatC := by
  intro K M _ _ _ _ _ _ σ s hs n P P' hsp
  have hc : ∀ x : K, σ.toRingEquiv.symm (algebraMap K M x) = algebraMap K M x := fun x => σ.symm.commutes x
  refine ⟨conjSrc σ.toRingEquiv.symm, conjSrc_injective _, fun w => GlobalTheory.DefU.ClassFin.under_conjSrc _ hc w,
    fun w => GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc _ w, Filter.Eventually.of_forall fun w B hB => ?_⟩
  have h := UpperTheory.CBC.SConjSatCAux.main σ.toRingEquiv s hs P P' hsp (conjSrc σ.toRingEquiv.symm w)
    ((CG.hasSat_mk _ _ _).1 hB)
  rw [UpperTheory.CBC.SConjSatCAux.conjSrc_conjSrc_symm] at h
  exact (CG.hasSat_mk _ _ _).2 h
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSGalAdEx
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.CBC.GaloisActionOnAdeles

variable {M : Type} [Field M]

theorem isometry_withAbs (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) :
    Isometry (WithAbs.congr v.1 w.1 τ) := by
  refine AddMonoidHomClass.isometry_of_norm (WithAbs.congr v.1 w.1 τ) fun x => ?_
  exact h _

def locMap (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) : v.Completion →+* w.Completion :=
  (InfinitePlace.Completion.equiv w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (WithAbs.congr v.1 w.1 τ).toRingHom
      (isometry_withAbs τ v w h).continuous).comp (InfinitePlace.Completion.equiv v).toRingHom)

theorem continuous_locMap (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) :
    Continuous (locMap τ v w h) :=
  (InfinitePlace.Completion.continuous_ofCompletion w).comp
    ((UniformSpace.Completion.continuous_map).comp (InfinitePlace.Completion.continuous_toCompletion v))

theorem locMap_coe (τ : M ≃+* M) (v w : InfinitePlace M) (h : ∀ x, w (τ x) = v x) (x : M) :
    locMap τ v w h (x : v.Completion) = ((τ x : M) : w.Completion) := by
  change InfinitePlace.Completion.ofCompletion ((UniformSpace.Completion.mapRingHom (WithAbs.congr v.1 w.1 τ).toRingHom
    (isometry_withAbs τ v w h).continuous) ((WithAbs.toAbs v.1 x : WithAbs v.1) : v.1.Completion)) = _
  exact congrArg InfinitePlace.Completion.ofCompletion (UniformSpace.Completion.mapRingHom_coe _ _)

theorem locMap_comp (τ τ' : M ≃+* M) (u v w : InfinitePlace M) (h : ∀ x, v (τ x) = u x) (h' : ∀ x, w (τ' x) = v x)
    (h'' : ∀ x, w ((τ.trans τ') x) = u x) (y : u.Completion) :
    locMap τ' v w h' (locMap τ u v h y) = locMap (τ.trans τ') u w h'' y := by
  induction y using InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq ((continuous_locMap _ _ _ _).comp (continuous_locMap _ _ _ _)) (continuous_locMap _ _ _ _)
  | ih a =>
    have e1 := locMap_coe τ u v h (WithAbs.equiv u.1 a)
    have e2 := locMap_coe τ' v w h' (τ (WithAbs.equiv u.1 a))
    have e3 := locMap_coe (τ.trans τ') u w h'' (WithAbs.equiv u.1 a)
    change locMap τ' v w h' (locMap τ u v h (WithAbs.equiv u.1 a : u.Completion)) = _
    rw [e1, e2]
    change _ = locMap (τ.trans τ') u w h'' (WithAbs.equiv u.1 a : u.Completion)
    rw [e3]
    rfl

theorem locMap_eq_self (τ : M ≃+* M) (hτ : ∀ x, τ x = x) (u : InfinitePlace M) (h : ∀ x, u (τ x) = u x)
    (y : u.Completion) : locMap τ u u h y = y := by
  induction y using InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_locMap _ _ _ _) continuous_id
  | ih a =>
    change locMap _ u u h (WithAbs.equiv u.1 a : u.Completion) = _
    rw [locMap_coe, hτ]
    rfl

def placePerm (σ : M ≃+* M) : InfinitePlace M ≃ InfinitePlace M where
  toFun w := w.comap σ.symm.toRingHom
  invFun w := w.comap σ.toRingHom
  left_inv w := InfinitePlace.ext _ _ fun x => by
    change ((w.comap σ.symm.toRingHom).comap σ.toRingHom) x = w x
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply]
    simp
  right_inv w := InfinitePlace.ext _ _ fun x => by
    change ((w.comap σ.toRingHom).comap σ.symm.toRingHom) x = w x
    rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply]
    simp

theorem placePerm_apply (σ : M ≃+* M) (w : InfinitePlace M) (x : M) : placePerm σ w (σ x) = w x := by
  rw [show placePerm σ w = w.comap σ.symm.toRingHom from rfl, InfinitePlace.comap_apply]
  simp

theorem placePerm_symm_apply (σ : M ≃+* M) (w : InfinitePlace M) (x : M) : w (σ.symm x) = placePerm σ w x := by
  rw [← placePerm_apply σ w (σ.symm x), RingEquiv.apply_symm_apply]

def locEquiv (σ : M ≃+* M) (w : InfinitePlace M) : w.Completion ≃+* (placePerm σ w).Completion where
  __ := locMap σ w (placePerm σ w) (placePerm_apply σ w)
  invFun := locMap σ.symm (placePerm σ w) w (placePerm_symm_apply σ w)
  left_inv y := by
    change locMap σ.symm (placePerm σ w) w (placePerm_symm_apply σ w)
      (locMap σ w (placePerm σ w) (placePerm_apply σ w) y) = y
    rw [locMap_comp σ σ.symm w (placePerm σ w) w _ _ (fun x => by simp)]
    exact locMap_eq_self _ (fun x => by simp) _ _ y
  right_inv y := by
    change locMap σ w (placePerm σ w) (placePerm_apply σ w)
      (locMap σ.symm (placePerm σ w) w (placePerm_symm_apply σ w) y) = y
    rw [locMap_comp σ.symm σ (placePerm σ w) w (placePerm σ w) _ _ (fun x => by simp)]
    exact locMap_eq_self _ (fun x => by simp) _ _ y

theorem continuous_locEquiv (σ : M ≃+* M) (w : InfinitePlace M) : Continuous (locEquiv σ w) :=
  continuous_locMap σ w (placePerm σ w) (placePerm_apply σ w)

def infEquiv (σ : M ≃+* M) : InfiniteAdeleRing M ≃+* InfiniteAdeleRing M :=
  (RingEquiv.piCongrRight fun w => locEquiv σ w).trans
    (RingEquiv.piCongrLeft (fun v : InfinitePlace M => v.Completion) (placePerm σ))

theorem continuous_infEquiv (σ : M ≃+* M) : Continuous (infEquiv σ) :=
  (Homeomorph.piCongrLeft (Y := fun v : InfinitePlace M => v.Completion) (placePerm σ)).continuous.comp
    (continuous_pi fun w => (continuous_locEquiv σ w).comp (continuous_apply w))

theorem infEquiv_algebraMap (σ : M ≃+* M) (x : M) :
    infEquiv σ (algebraMap M (InfiniteAdeleRing M) x) = algebraMap M (InfiniteAdeleRing M) (σ x) := by
  funext v
  obtain ⟨w, rfl⟩ := (placePerm σ).surjective v
  change (Equiv.piCongrLeft (fun v : InfinitePlace M => v.Completion) (placePerm σ)
    (fun w => locEquiv σ w (algebraMap M (InfiniteAdeleRing M) x w))) (placePerm σ w) = _
  rw [Equiv.piCongrLeft_apply_apply]
  exact locMap_coe σ w (placePerm σ w) (placePerm_apply σ w) x

variable [NumberField M]

theorem conjFin_symm_conjFin (σ : M ≃+* M) (y : Af M) : conjFin σ.symm (conjFin σ y) = y := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField M
  refine congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := M)).equalizer
    ((continuous_conjFin _).comp (continuous_conjFin _)) continuous_id (funext fun k => ?_)) y
  simp only [Function.comp_apply, id]
  rw [conjFin_algebraMap, conjFin_algebraMap, RingEquiv.symm_apply_apply]

def finEquiv (σ : M ≃+* M) : Af M ≃+* Af M where
  __ := conjFin σ
  invFun := conjFin σ.symm
  left_inv y := conjFin_symm_conjFin σ y
  right_inv y := by simpa using conjFin_symm_conjFin σ.symm y

end UpperTheory.CBC.GaloisActionOnAdeles

open UpperTheory.CBC.GaloisActionOnAdeles in

def UpperTheory.CBC.SGalAdEx : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] (σ : M ≃+* M), ∃ s : Ad M ≃+* Ad M, UpperTheory.CBC.IsGalAd σ s

open UpperTheory.CBC.GaloisActionOnAdeles in
theorem UpperTheory.CBC.SGalAdEx_holds : UpperTheory.CBC.SGalAdEx := by
  intro M _ _ σ
  refine ⟨RingEquiv.prodCongr (infEquiv σ) (finEquiv σ), ?_, fun x => ?_, fun x => rfl⟩
  · exact (continuous_infEquiv σ).prodMap (continuous_conjFin σ)
  · exact Prod.ext (infEquiv_algebraMap σ x) (conjFin_algebraMap σ x)
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSIsoSat
section
noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.CBC

theorem SIsoSat_holds : SIsoSat := by
  intro F _ _ n π π' h w B hB
  cases π with
  | cx p =>
    cases π' with
    | cx p' =>
      exact (GlobalTheory.CuspRep.CG.hasSat_mk p' w B).2
        (GlobalTheory.CuspRep.CuspSub.Iso.hasSatGL (π := p) (π' := p') h ((GlobalTheory.CuspRep.CG.hasSat_mk p w B).1 hB))
    | re p' => exact h.elim
  | re p =>
    cases π' with
    | cx p' => exact h.elim
    | re p' => exact UpperTheory.V.TR.CuspSub.Iso.hasSat (π := p) (π' := p') h hB

end UpperTheory.CBC
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSNormPow
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

private theorem UpperTheory.CBC.NormPowerUnderPlace.normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (w : HeightOneSpectrum (𝓞 K')) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem UpperTheory.CBC.SNormPow_holds : UpperTheory.CBC.SNormPow := by
  intro K M _ _ _ _ _ w
  exact ⟨_, UpperTheory.CBC.NormPowerUnderPlace.normV_under (K := K) w⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.PSSmo
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC.SmoothnessOfSatakeParameters

theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem cx_smo (hJ : GlobalTheory.Published.JacquetShalikaRigidity) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    {a : ℕ} (ha : 1 ≤ a) (π π' : CG E a)
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B ∧ π'.HasSat w B) : π = π' := by
  obtain ⟨s, hs⟩ := hJ E Unit Unit (fun _ => a) (fun _ => a) (fun _ => π) (fun _ => π') (fun _ => ha) (fun _ => ha)
    (hw.mono fun w ⟨B, h1, h2⟩ => ⟨fun _ => B, fun _ => B, fun _ => h1, fun _ => h2, rfl⟩)
  exact eq_of_heq (Sigma.mk.inj (hs ())).2

end UpperTheory.CBC.SmoothnessOfSatakeParameters
end
end

