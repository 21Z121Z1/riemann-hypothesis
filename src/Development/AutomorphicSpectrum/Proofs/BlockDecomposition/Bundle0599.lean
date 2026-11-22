import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0417
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0373
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0532
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0564
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0571
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0097
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0584
import GroundTheory.AutomorphicForms.Bundle0010
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0575
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionOpenCellModuloWhittaker
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.Bad

section Gen

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  {P : Subgroup G} {τ : Representation ℂ P W}

theorem isClopen_supp (f : smoothPart (ind P τ)) : IsClopen {g | f.1.1 g ≠ 0} := by
  have ho : IsOpen {g : G | ind P τ g f.1 = f.1} := f.2
  have hlc : IsLocallyConstant f.1.1 := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x =>
      ⟨(fun y => x⁻¹ * y) ⁻¹' {g | ind P τ g f.1 = f.1}, ho.preimage (by fun_prop), ?_, ?_⟩
    · show ind P τ (x⁻¹ * x) f.1 = f.1
      simp
    · intro y hy
      have h : f.1.1 (x * (x⁻¹ * y)) = f.1.1 x := congrFun (congrArg Subtype.val hy) x
      rwa [mul_inv_cancel_left] at h
  exact (hlc.isClopen_fiber 0).compl

theorem ne_zero_left (f : smoothPart (ind P τ)) (p : P) (g : G) (hg : f.1.1 g ≠ 0) : f.1.1 (p * g) ≠ 0 := by
  intro h
  have h1 : τ p (f.1.1 g) = 0 := (f.1.2 p g).symm.trans h
  apply hg
  have h2 := congrArg (τ p⁻¹) h1
  rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
  exact h2

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cell_mul {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N} {w : Equiv.Perm (Fin N)} {g n : GL (Fin N) k}
    (hg : g ∈ cell k d hd w) (hn : n ∈ unipB k (Fin N)) : g * n ∈ cell k d hd w := by
  obtain ⟨p, hp, m, hm, rfl⟩ := hg
  exact ⟨p, hp, m * n, mul_mem hm hn, by simp only [mul_assoc]⟩

theorem kill_cell (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {h N : ℕ} (d : Fin h → ℕ)
    (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ)
    (w : Equiv.Perm (Fin N)) (hbad : cell k d hd w ≠ cell k d hd (wOpen d hd))
    (hcl : IsClosed ({g | f.1.1 g ≠ 0} ∩ cell k d hd w)) :
    ∃ f' : IndSp (stdBlocks d hd) ρ,
      f - f' ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧
      (∀ g, f'.1.1 g ≠ 0 → ∃ n ∈ unipB k (Fin N), f.1.1 (g * n) ≠ 0) ∧
      ∀ g ∈ cell k d hd w, f'.1.1 g = 0 := by
  classical
  obtain ⟨L, hLm, hLc, hLU, hLex⟩ := GlobalTheory.CompanionTheory.UnipExhaust.exists_monotone_compact_exhaustion k N (unipB k (Fin N)) le_rfl
    GlobalTheory.LocLanglands.InvInt.isClosed_unipB
  have hcellL : cell k d hd w =
      {g | ∃ p ∈ parab k (stdBlocks d hd), ∃ j, ∃ n ∈ L j, g = p * pm k w * n} := by
    ext g
    constructor
    · rintro ⟨p, hp, n, hn, rfl⟩
      obtain ⟨j, hj⟩ := hLex n hn
      exact ⟨p, hp, j, n, hj, rfl⟩
    · rintro ⟨p, hp, j, n, hn, rfl⟩
      exact ⟨p, hp, n, hLU j hn, rfl⟩
  have : T2Space (GL (Fin N) k) := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
    infer_instance
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.BaireCoset.baire_double_coset (parab k (stdBlocks d hd))
    (GlobalTheory.WhitHered.CellLoc.isClosed_parab (stdBlocks d hd)) (GlobalTheory.SplitWeil.KO k (Fin N) : Set (GL (Fin N) k)) GlobalTheory.SplitFlip.isCompact_KO
    (fun g => by
      obtain ⟨p, c, hc, e⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul (stdBlocks d hd) g
      exact ⟨p, p.2, c, hc, e⟩)
    L hLm hLc (pm k w) {g | f.1.1 g ≠ 0} (isClopen_supp f).isOpen
    (fun p hp g hg => ne_zero_left f ⟨p, hp⟩ g hg) (by rw [← hcellL]; exact hcl)
  obtain ⟨i, j, hij, hb⟩ := (exists_adjacent_blk_lt_or_cell_eq_open k h N d hd w).resolve_right hbad
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hψ1 (by ext x; simp [hc x])
  obtain ⟨u, hu, hwu, hrad⟩ := GlobalTheory.CompanionTheory.Rodier.RootElt.exists_root_conj_mem_unipRad k ψ h N d hd w i j hij hb t
  obtain ⟨j₁, hj₁⟩ := hLex u hu
  have hJ0 : L j₀ ≤ L (max j₀ j₁) := hLm (le_max_left _ _)
  have hJ1 : L j₁ ≤ L (max j₀ j₁) := hLm (le_max_right _ _)
  generalize max j₀ j₁ = J at hJ0 hJ1
  let θ : L J →* ℂˣ := (whitChar ψ N).comp (Subgroup.inclusion (hLU J))
  have hθ : IsOpen (θ.ker : Set (L J)) :=
    (GlobalTheory.Whittaker.isSmoothChar_whitChar hψ).preimage
      (Continuous.subtype_mk continuous_subtype_val _ : Continuous (Subgroup.inclusion (hLU J)))
  obtain ⟨f', h1, h2, h3⟩ := GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd (parab k (stdBlocks d hd)) _ (L J) (hLc J) θ hθ f
  have hu' : u ∈ L J := hJ1 hj₁
  have hfw : f'.1.1 (pm k w) = 0 := by
    have e1 := h3 ⟨u, hu'⟩ (pm k w)
    have hθu : θ ⟨u, hu'⟩ = Circle.toUnits (ψ t) := hwu
    have hq : leviProj k (stdBlocks d hd) ⟨_, unipRad_le_parab k _ hrad⟩ = 1 :=
      (coe_mem_unipRad k (⟨_, unipRad_le_parab k _ hrad⟩ : parab k (stdBlocks d hd))).1 hrad
    have e2 := parInd_law (stdBlocks d hd) ρ f' ⟨_, unipRad_le_parab k _ hrad⟩ (pm k w)
    rw [hq] at e2
    simp only [map_one, Units.val_one, one_smul, Module.End.one_apply, inv_mul_cancel_right] at e2
    rw [e2] at e1
    rw [hθu] at e1
    have hne : ((Circle.toUnits (ψ t) : ℂˣ) : ℂ) ≠ 1 := fun e => ht (Circle.ext (by simpa using e))
    have h0 : (((Circle.toUnits (ψ t) : ℂˣ) : ℂ) - 1) • f'.1.1 (pm k w) = 0 := by
      rw [sub_smul, one_smul, ← e1, sub_self]
    exact (smul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)
  refine ⟨f', ?_, ?_, ?_⟩
  · refine (Submodule.span_mono ?_) h1
    rintro _ ⟨n, v, rfl⟩
    exact ⟨⟨n.1, hLU J n.2⟩, v, rfl⟩
  · intro g hg
    obtain ⟨l, hl, hne⟩ := h2 g hg
    exact ⟨l, hLU J hl, hne⟩
  · intro g hg
    by_contra hne
    obtain ⟨l, hl, hfl⟩ := h2 g hne
    have hgl := cell_mul hg (hLU J hl)
    obtain ⟨p, hp, n, hn, e⟩ := hj₀ (g * l) hfl (by rw [hcellL] at hgl; exact hgl)
    have hl2 : n * l⁻¹ ∈ L J := mul_mem (hJ0 hn) (inv_mem hl)
    have hg' : g = (⟨p, hp⟩ : parab k (stdBlocks d hd)) * (pm k w * (n * l⁻¹)) := by
      show g = p * (pm k w * (n * l⁻¹))
      rw [← mul_assoc, ← mul_assoc, ← e]
      group
    apply hne
    have e3 := h3 ⟨_, hl2⟩ (pm k w)
    rw [hfw, smul_zero] at e3
    rw [hg', f'.1.2 ⟨p, hp⟩, e3, map_zero]

end GlobalTheory.CompanionTheory.Rodier.Bad

namespace GlobalTheory.CompanionTheory.Rodier

open Bad in

theorem exists_open_congr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (f : IndSp (stdBlocks d hd) ρ),
    ∃ f₀ ∈ openFns d hd ρ, f - f₀ ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ hψ1 h N d hd W _ _ ρ f
  classical
  obtain ⟨hcov, ht, hconst, hclos, hmax⟩ := GlobalTheory.CompanionTheory.Rodier.CellOrder.cells_main k h N d hd
  let bad : IndSp (stdBlocks d hd) ρ → Finset (Equiv.Perm (Fin N)) := fun f =>
    Finset.univ.filter fun w => cell k d hd w ≠ cell k d hd (wOpen d hd) ∧ ∃ g ∈ cell k d hd w, f.1.1 g ≠ 0
  have mem_bad : ∀ f w, w ∈ bad f ↔
      cell k d hd w ≠ cell k d hd (wOpen d hd) ∧ ∃ g ∈ cell k d hd w, f.1.1 g ≠ 0 := fun f w => by
    simp [bad]
  suffices H : ∀ n, ∀ f, (bad f).card = n → ∃ f₀ ∈ openFns d hd ρ,
      f - f₀ ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) from H _ f rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn
  rcases (bad f).eq_empty_or_nonempty with hE | hne
  · refine ⟨f, ?_, by simp⟩
    intro g hg
    obtain ⟨w, hw⟩ := hcov g
    by_contra hno
    have hb : w ∈ bad f := (mem_bad f w).2 ⟨fun e => hno (e ▸ hw), g, hw, hg⟩
    simp [hE] at hb
  · obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image (bad f) (fun w => ht (pm k w)) hne
    obtain ⟨hbad, hmet⟩ := (mem_bad f w).1 hw
    have hcl : IsClosed ({g | f.1.1 g ≠ 0} ∩ cell k d hd w) := by
      refine isClosed_of_closure_subset fun x hx => ?_
      have hxS : x ∈ {g | f.1.1 g ≠ 0} :=
        (isClopen_supp f).isClosed.closure_subset_iff.2 Set.inter_subset_left hx
      refine ⟨hxS, ?_⟩
      rcases hclos w (closure_mono Set.inter_subset_right hx) with hC | hlt
      · exact hC
      · exfalso
        have hlt' : ht x < ht (pm k w) := hlt
        obtain ⟨w', hw'⟩ := hcov x
        by_cases ho : cell k d hd w' = cell k d hd (wOpen d hd)
        · have h1 : ht x = ht (pm k (wOpen d hd)) := by
            rw [hconst w' x hw']
            refine (hconst w' _ ?_).symm
            rw [ho]
            exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
          have := hmax w hbad
          omega
        · have h1 := hmin w' ((mem_bad f w').2 ⟨ho, x, hw', hxS⟩)
          have h2 := hconst w' x hw'
          omega
    obtain ⟨f', h1, h2, h3⟩ := kill_cell ψ hψ hψ1 d hd ρ f w hbad hcl
    have hsub : bad f' ⊂ bad f := by
      refine (Finset.ssubset_iff_of_subset fun w' hw' => ?_).2 ⟨w, hw, fun hw' => ?_⟩
      · obtain ⟨hb, g, hg, hfg⟩ := (mem_bad f' w').1 hw'
        obtain ⟨n, hn, hfn⟩ := h2 g hfg
        exact (mem_bad f w').2 ⟨hb, g * n, cell_mul hg hn, hfn⟩
      · obtain ⟨_, g, hg, hfg⟩ := (mem_bad f' w).1 hw'
        exact hfg (h3 g hg)
    have hlt : (bad f').card < n := hn ▸ Finset.card_lt_card hsub
    obtain ⟨f₀, hf₀, h4⟩ := ih _ hlt f' rfl
    refine ⟨f₀, hf₀, ?_⟩
    have := add_mem h1 h4
    simpa using this

end GlobalTheory.CompanionTheory.Rodier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvolutionCompatiblePolynomial
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.HermFixed

theorem dvd_of_monic_irreducible_factors {K : Type} [Field K] {P d : K[X]} (hs : P.Separable)
    (h : ∀ Q : K[X], Q.Monic → Irreducible Q → Q ∣ P → Q ∣ d) : P ∣ d := by
  by_cases hd : d = 0
  · simp [hd]
  have hP0 : P ≠ 0 := hs.ne_zero
  have hnd : (UniqueFactorizationMonoid.normalizedFactors P).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hs.squarefree
  refine (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP0 hd).2 ?_
  refine (Multiset.le_iff_subset hnd).2 fun Q hQ => ?_
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
  have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
  have hmon : Q.Monic := by
    rw [← hnorm]
    exact Polynomial.monic_normalize hirr.ne_zero
  have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ
  exact UniqueFactorizationMonoid.mem_normalizedFactors_iff' hd |>.2 ⟨hirr, hnorm, h Q hmon hirr hdvd⟩

theorem dvd_map_comp_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
    (m r₀ : E[X]) (hr : Q.1 ∣ X * r₀ - 1)
    (hfix : invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) :
    Q.1 ∣ (m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m := by
  have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 hr
  rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
  have hR : AdjoinRoot.mk Q.1 r₀ = (AdjoinRoot.root Q.1)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hinv : invol Q (AdjoinRoot.mk Q.1 m : Fld Q)
      = AdjoinRoot.mk Q.1 ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀) := by
    show AdjoinRoot.lift ((AdjoinRoot.of Q.1).comp (IsCMField.complexConj E : E →+* E)) (AdjoinRoot.root Q.1)⁻¹
      (eval₂_conj_inv_root Q) (AdjoinRoot.mk Q.1 m) = _
    rw [AdjoinRoot.lift_mk, ← hR, Polynomial.comp, Polynomial.hom_eval₂, eval₂_map]
    rfl
  have heq : AdjoinRoot.mk Q.1 ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀)
      = AdjoinRoot.mk Q.1 m := hinv.symm.trans hfix
  refine AdjoinRoot.mk_eq_zero.1 ?_
  rw [map_sub, heq, sub_self]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) := by
  intro E _ _ _ n γ₀ hell H₀ hH _ hiso m hfix
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  have hAB : aeval γ₀.val r₀ * γ₀.val = 1 := by rw [← hr₀, Units.inv_mul]
  have key := GlobalTheory.CompanionTheory.AdjointPoly.cT_aeval_mul_eq E (IsCMField.complexConj E).toRingEquiv.toRingHom n
    γ₀.val H₀ r₀ hiso hAB m
  have hdvd : γ₀.val.charpoly ∣
      (m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m :=
    dvd_of_monic_irreducible_factors hsep fun Q hmon hirr hQ =>
      dvd_map_comp_sub ⟨Q, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell Q hmon hirr hQ⟩ m r₀
        (hQ.trans hPr) (hfix _ ⟨Q, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell Q hmon hirr hQ⟩ hQ)
  have heq : aeval γ₀.val ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀)
      = aeval γ₀.val m := by
    obtain ⟨t, ht⟩ := hdvd
    have h0 : aeval γ₀.val ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m) = 0 := by
      rw [ht, map_mul, Matrix.aeval_self_charpoly, zero_mul]
    rwa [map_sub, sub_eq_zero] at h0
  have hH' : cT (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ = H₀ := hH
  have hmul : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m)
      = cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ₀.val m)
        * cT (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ := by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  show cT (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) = H₀ * aeval γ₀.val m
  rw [hmul, hH', key, heq]

end GlobalTheory.CompanionTheory.HermFixed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFundamentalDomainRangeProdMap
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.PairDom

theorem isFundamentalDomain_range_prodMap {A B X Y : Type} [Group A] [Group B] [Group X] [Group Y]
    [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalGroup X] [IsTopologicalGroup Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant] (f : A →* X) (g : B →* Y) (F : Set X) (G : Set Y)
    (hF : IsFundamentalDomain f.range F μ) (hG : IsFundamentalDomain g.range G ν) :
    IsFundamentalDomain (f.prodMap g).range (F ×ˢ G) (μ.prod ν) := by
  have hmp : ∀ z : X × Y, MeasurePreserving (z * ·) (μ.prod ν) (μ.prod ν) := fun z =>
    measurePreserving_mul_left (μ.prod ν) z
  refine IsFundamentalDomain.mk'' (hF.nullMeasurableSet.prod hG.nullMeasurableSet) ?_ ?_
    (fun γ => (hmp γ).quasiMeasurePreserving)
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hF.ae_covers,
      Measure.quasiMeasurePreserving_snd.ae hG.ae_covers] with z h1 h2
    obtain ⟨⟨_, a, rfl⟩, ha⟩ := h1
    obtain ⟨⟨_, b, rfl⟩, hb⟩ := h2
    exact ⟨⟨(f a, g b), (a, b), rfl⟩, ha, hb⟩
  · rintro ⟨_, ⟨a, b⟩, rfl⟩ hγ
    by_cases ha : f a = 1
    · have hb : (⟨g b, b, rfl⟩ : g.range) ≠ 1 := by
        intro h
        apply hγ
        apply Subtype.ext
        exact Prod.ext ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).preimage_null (hG.aedisjoint hb)
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.2, hw.2, rfl⟩, ⟨_, hz.2, one_smul _ _⟩⟩
    · have ha' : (⟨f a, a, rfl⟩ : f.range) ≠ 1 := by
        intro h
        exact ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).preimage_null (hF.aedisjoint ha')
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.1, hw.1, rfl⟩, ⟨_, hz.1, one_smul _ _⟩⟩

theorem exists_measure_of_eq {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup X] [IsTopologicalGroup Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (μ₁ : Measure X) (μ₂ : Measure Y)
    [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [μ₁.IsMulRightInvariant] [μ₂.IsMulRightInvariant]
    (Γ : Subgroup (X × Y)) (F : Set (X × Y)) (hF : IsFundamentalDomain Γ F (μ₁.prod μ₂))
    (m : MeasurableSpace (X × Y)) (e : Prod.instMeasurableSpace = m) :
    ∃ μ : @Measure (X × Y) m,
      (@Measure.IsMulLeftInvariant _ m _ μ ∧ @Measure.IsMulRightInvariant _ m _ μ ∧
        @Measure.IsOpenPosMeasure _ _ m μ ∧ @IsLocallyFiniteMeasure _ m _ μ) ∧
      @IsFundamentalDomain Γ (X × Y) _ _ m F μ ∧
      ∀ f : X × Y → ℂ, @integral _ _ _ _ m (@Measure.restrict _ m μ F) f =
        @integral _ _ _ _ Prod.instMeasurableSpace ((μ₁.prod μ₂).restrict F) f := by
  subst e
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  exact ⟨μ₁.prod μ₂, ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hF, fun _ => rfl⟩

theorem isMulRightInvariant_GA (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    [m : MeasurableSpace (GA E a)] [hm : BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  obtain ⟨ν, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have e : m = CuspidalL2GL.measurableSpace_GA E a := hm.measurable_eq
  subst e
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  infer_instance

theorem prodDom : RatProper → ProdDom := by
  intro _ E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ h₁ h₂
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI := isMulRightInvariant_GA E a μ₁
  haveI := isMulRightInvariant_GA E b μ₂
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨μ, hh, hf, hi⟩ := exists_measure_of_eq μ₁ μ₂ (ratH E a b) (F₁ ×ˢ F₂)
    (isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ h₁ h₂) (borelH E a b)
    Prod.borelSpace.measurable_eq
  exact ⟨⟨μ, hh, F₁ ×ˢ F₂, hf⟩, rfl, fun f => hi f⟩

end GlobalTheory.CompanionTheory.PairDom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbitStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnder_of_same_orbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder w z → SameOrbit z' z → IsUnder w z' := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Orbit.isUnder_of_sameOrbit | exact GlobalTheory.CompanionTheory.MixZ.Orbit.isUnder_of_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.MixZ.Orbit.isUnder_of_sameOrbit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHolds
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem sphericalProduct_A4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  intro G _ _ _
  unfold PositivityTheory.SphericalProduct.A4
  intro D V _ _ π hπ hex
  obtain ⟨t, ht⟩ := hex
  refine ⟨fun v => GlobalTheory.CompanionTheory.Cass.proj_mem_fixed_piN G D V π v, ?_⟩
  have hsm : GlobalTheory.PRep.IsSmooth π := by
    unfold GlobalTheory.PRep.IsAdmissible at hπ
    exact hπ.1
  have hH := GlobalTheory.T.hecke_character_exists_unique
  unfold PositivityTheory.Lbc.HeckeExistsUnique at hH
  obtain ⟨U, hU, -⟩ := hH G D.J D.isOpen_J D.isCompact_J V π hsm (t : G)
  exact GlobalTheory.T.jacquet_projection_surjective_holds G D V π hπ t ht U hU

end GlobalTheory.CompanionTheory.Cass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosOfSocle
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SocleFrob

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_smul_id {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin n) k) X) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (φ : X →ₗ[ℂ] X) (hφ : ∀ g x, φ (ρ g x) = ρ g (φ x)) : ∃ c : ℂ, φ = c • LinearMap.id := by
  haveI : ρ.IsIrreducible := hi
  have hs' : GroundTheory.Automorphic.IsSmooth ρ := hs
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hs').2
    (⟨φ, fun g => LinearMap.ext fun x => hφ g x⟩ : Representation.IntertwiningMap ρ ρ)
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  exact (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hc).symm

theorem isIrreducible_piTensor {h : ℕ} (x : Fin h → IrrGL k) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    exists_eq_smul_id _ (x a).2.rep.smooth (x a).2.rep.irr φ hφ

theorem jm_ne_zero_of_isSocle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    (∀ a, 0 < (x a).1) → IsSocle π (prodIrr x hd) → Zc.jm x hd π ≠ 0 := by
  intro k _ _ _ _ h N x hd V _ _ π _ _ hS
  obtain ⟨hi, f, hf, -⟩ := hS
  haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 : 1 ≤ Zc.jm x hd π :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac (stdBlocks (fun a => (x a).1) hd) (isIrreducible_piTensor x) f
      ⟨v, fun h0 => hv (hf (h0.trans (map_zero f).symm))⟩
  exact ENat.one_le_iff_ne_zero.1 h1

end GlobalTheory.CompanionTheory.SocleFrob

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_pos : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ → ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  first | exact @GlobalTheory.CompanionTheory.FrobJm.one_le_jm | exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm | (intros; apply GlobalTheory.CompanionTheory.FrobJm.one_le_jm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2Statement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_skew_adjoint_l2 : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.CuspRep.Lie E a) (φ ψ : Sm E a) (hφ : MemL2Quotient (latticeGL E a) μ φ.1) (hψ : MemL2Quotient (latticeGL E a) μ ψ.1) (hXφ : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1) (hXψ : MemL2Quotient (latticeGL E a) μ (lie E a X ψ).1), Continuous φ.1 → Continuous ψ.1 → Continuous (lie E a X φ).1 → Continuous (lie E a X ψ).1 → inner ℂ hXφ.toL2 hψ.toL2 = - inner ℂ hφ.toL2 hXψ.toL2 := by
  first | exact @GlobalTheory.CompanionTheory.LieSkew.lie_skew | exact GlobalTheory.CompanionTheory.LieSkew.lie_skew | (intros; apply GlobalTheory.CompanionTheory.LieSkew.lie_skew <;> assumption)
end

