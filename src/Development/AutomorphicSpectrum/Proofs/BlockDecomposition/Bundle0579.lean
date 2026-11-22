import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1399
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosed
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.LowerOpen

theorem inv_conj_apply {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (x : GL (Fin N) k)
    (p q : Fin N) :
    (((GroundTheory.Automorphic.permGL k w)⁻¹ * x * GroundTheory.Automorphic.permGL k w : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (w p) (w q) := by
  have h1 : (((GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      w.permMatrix k := by
    rw [← map_inv]
    show ((w⁻¹)⁻¹).permMatrix k = w.permMatrix k
    rw [inv_inv]
  have h2 : ((GroundTheory.Automorphic.permGL k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (w⁻¹).permMatrix k := rfl
  rw [Units.val_mul, Units.val_mul, h1, h2, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Equiv.Perm.inv_def]

theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd q) < blk (stdBlocks d hd) (wOpen d hd p)) : p < q := by
  by_contra hpq
  have h1 := Tuple.monotone_sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) (not_lt.mp hpq)
  simp only [Function.comp_apply, GlobalTheory.CompanionTheory.Rodier.wKey] at h1
  have hb' : blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) q) <
      blk (stdBlocks d hd) (Tuple.sort (GlobalTheory.CompanionTheory.Rodier.wKey d hd) p) := hb
  rw [Prod.Lex.toLex_le_toLex] at h1
  rcases h1 with h | ⟨h, -⟩
  · exact lt_asymm hb' (OrderDual.toDual_lt_toDual.mp h)
  · exact (ne_of_lt hb') (OrderDual.toDual.injective h)

theorem lower_entries {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) (i j : Fin N) :
    (blk (stdBlocks d hd) i < blk (stdBlocks d hd) j → (x : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      (blk (stdBlocks d hd) i = blk (stdBlocks d hd) j →
        (x : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) := by
  obtain ⟨hpl, hdiag⟩ := (GlobalTheory.SmGL.mem_unipRadLower k).mp hx
  rw [GlobalTheory.SmGL.mem_parabLower_iff] at hpl
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j'⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  refine ⟨fun hab => hpl a b i' j' hab, fun hab => ?_⟩
  subst hab
  rw [hdiag a i' j', Matrix.one_apply, Matrix.one_apply]
  simp [(stdBlocks d hd).apply_eq_iff_eq]

theorem parab_inf_lower {k : Type} [Field k] {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
    {x : GL (Fin N) k} (hp : x ∈ parab k (stdBlocks d hd))
    (hx : x ∈ unipRadLower k (stdBlocks d hd)) : x = 1 := by
  ext i j
  rcases lt_trichotomy (blk (stdBlocks d hd) i) (blk (stdBlocks d hd) j) with hlt | heq | hgt
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [(lower_entries hx i j).1 hlt]
    simp [Matrix.one_apply, hij]
  · rw [(lower_entries hx i j).2 heq]
    simp
  · have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hgt
    rw [GlobalTheory.SmGL.mem_parab.mp hp i j hgt]
    simp [Matrix.one_apply, hij]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

variable {k d hd} in

theorem mem_unipU_iff {u : GL (Fin N) k} :
    u ∈ unipU k d hd ↔ u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  rw [GlobalTheory.CompanionTheory.Rodier.unipU, Subgroup.mem_inf, Subgroup.mem_comap]
  rfl

theorem inv_conj_mem_unipU {x : GL (Fin N) k} (hx : x ∈ unipRadLower k (stdBlocks d hd)) :
    (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd := by
  rw [mem_unipU_iff]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.SmGL.mem_unipB]
    have hent : ∀ p q, (((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) p q = (x : Matrix (Fin N) (Fin N) k) (wOpen d hd p) (wOpen d hd q) :=
      fun p q => inv_conj_apply (wOpen d hd) x p q
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hent]
      rcases lt_trichotomy (blk (stdBlocks d hd) (wOpen d hd i)) (blk (stdBlocks d hd) (wOpen d hd j))
        with hlt | heq | hgt
      · exact (lower_entries hx _ _).1 hlt
      · rw [(lower_entries hx _ _).2 heq, Matrix.one_apply, if_neg]
        intro h
        exact hji.ne' ((wOpen d hd).injective h)
      · exact absurd (lt_of_blk_lt d hd hgt) (not_lt.mpr hji.le)
    · rw [hent, (lower_entries hx _ _).2 rfl]
      simp
  · have he : pm k (wOpen d hd) * ((pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd)) *
        (pm k (wOpen d hd))⁻¹ = x := by group
    rw [he]
    exact hx

theorem eq_of_mul_eq {p u u' : GL (Fin N) k} (hp : p ∈ parab k (stdBlocks d hd))
    (hu : u ∈ unipU k d hd) (hu' : u' ∈ unipU k d hd)
    (e : p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u') : u = u' := by
  have hv : u' * u⁻¹ ∈ unipU k d hd := (unipU k d hd).mul_mem hu' ((unipU k d hd).inv_mem hu)
  have hlow := (mem_unipU_iff.mp hv).2
  have hpeq : pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹ = p := by
    calc pm k (wOpen d hd) * (u' * u⁻¹) * (pm k (wOpen d hd))⁻¹
        = (pm k (wOpen d hd) * u') * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by group
      _ = (p * pm k (wOpen d hd) * u) * u⁻¹ * (pm k (wOpen d hd))⁻¹ := by rw [e]
      _ = p := by group
  rw [hpeq] at hlow
  have h1 := parab_inf_lower hp hlow
  rw [h1] at e
  simpa using e

theorem isClosed_unipU : IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  have hent : ∀ (i j : Fin N) (c : k),
      IsClosed {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = c} :=
    fun i j c => isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
  have hB : IsClosed (unipB k (Fin N) : Set (GL (Fin N) k)) := by
    have hs : (unipB k (Fin N) : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, ⋂ (_ : j < i), {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = 0}) ∩
          ⋂ i, {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i i = 1} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipB]
    rw [hs]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => hent i j 0).inter
      (isClosed_iInter fun i => hent i i 1)
  have hL : IsClosed (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    have hs : (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) =
        (⋂ a, ⋂ b, ⋂ i, ⋂ j, ⋂ (_ : a < b), {g : GL (Fin N) k |
          (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨b, j⟩) = 0}) ∩
          ⋂ a, ⋂ i, ⋂ j, {g : GL (Fin N) k |
            (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩) =
              (1 : Matrix (Fin (d a)) (Fin (d a)) k) i j} := by
      ext g
      simp [GlobalTheory.SmGL.mem_unipRadLower, GlobalTheory.SmGL.mem_parabLower_iff]
    rw [hs]
    exact (isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ => hent _ _ _).inter
      (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j => hent _ _ _)
  have hc : Continuous fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hs : (unipU k d hd : Set (GL (Fin N) k)) =
      (unipB k (Fin N) : Set (GL (Fin N) k)) ∩
        (fun u : GL (Fin N) k => pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) ⁻¹'
          (unipRadLower k (stdBlocks d hd) : Set (GL (Fin N) k)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    exact mem_unipU_iff
  rw [hs]
  exact hB.inter (hL.preimage hc)

end GlobalTheory.CompanionTheory.Rodier.LowerOpen

namespace GlobalTheory.CompanionTheory.Rodier

theorem unipU_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ x ∈ unipRadLower k (stdBlocks d hd), (pm k (wOpen d hd))⁻¹ * x * pm k (wOpen d hd) ∈ unipU k d hd) ∧ (∀ p ∈ parab k (stdBlocks d hd), ∀ u ∈ unipU k d hd, ∀ u' ∈ unipU k d hd, p * pm k (wOpen d hd) * u = pm k (wOpen d hd) * u' → u = u') ∧ IsClosed (unipU k d hd : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun x hx => LowerOpen.inv_conj_mem_unipU k d hd hx,
    fun p hp u hu u' hu' e => LowerOpen.eq_of_mul_eq k d hd hp hu hu' e,
    LowerOpen.isClosed_unipU k d hd⟩

end GlobalTheory.CompanionTheory.Rodier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdUniformizerEqOne
section
open Ad3 Ad3.S
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)
open GroundTheory.Global.RationalSymbol (prime)

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegral

theorem pOf_eq_prime (v : Pl) : pOf v = prime v := by
  show Ideal.absNorm v.asIdeal = prime v
  rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
  have h : ((prime v : ℕ) : NumberField.RingOfIntegers ℚ) =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) ((prime v : ℕ) : ℤ) := by
    simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
  simp

theorem ord_uniformizer_eq_one (v : Pl) :
    ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v) = 1 := by
  have h1 : Valued.v ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) = WithZero.exp (-1) :=
    DirichletHecke.valued_uniformizer v
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord (K := ℚ) (v := v)
    (x := ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (Units.ne_zero _)
  have h3 : WithZero.exp (-ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v)) = WithZero.exp (-1) :=
    h2.symm.trans h1
  have h4 := WithZero.exp_injective h3
  omega

theorem coe_localChar_unifUnit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (v : Pl)
    (hv : ¬ prime v ∣ N) :
    χ (prime v : ZMod N) = (localChar (DirichletHecke.heckeCharacter χ) v (unifUnit (Qv v)) : ℂ) := by
  obtain ⟨a, ha⟩ : ∃ a : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ,
      a = unifUnit (Qv v) * (DirichletHecke.uniformizer v)⁻¹ := ⟨_, rfl⟩
  have h1 := ord_units_mul (K := Qv v) (unifUnit (Qv v)) (DirichletHecke.uniformizer v)⁻¹
  have h2 := ord_units_inv (K := Qv v) (DirichletHecke.uniformizer v)
  have h3 := ord_unifUnit (K := Qv v)
  have h4 := ord_uniformizer_eq_one v
  have hord : ord ((unifUnit (Qv v) * (DirichletHecke.uniformizer v)⁻¹ : (Qv v)ˣ) : Qv v) = 0 := by
    rw [h1, h2, h3, h4]; norm_num
  have hval : Valued.v ((a : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) = 1 := by
    rw [ha]
    exact (GroundTheory.Global.valued_eq_one_iff_ord (Units.ne_zero _)).2 hord
  have hmem : a ∈ (Submonoid.ofClass
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)).units := by
    simp only [Submonoid.mem_units_iff, Units.val_inv_eq_inv_val]
    constructor
    · change ((a : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hval.le
    · change ((a : IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v))⁻¹ ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  have hnorm := DirichletHecke.norm_padicRingEquiv_eq_one hmem
  have htriv := DirichletHecke.heckeCharacter_finiteEmbedding_of_not_dvd χ hv hnorm
  have hunif := DirichletHecke.coe_heckeCharacter_uniformizer χ hv
  have hπ : (unifUnit (Qv v) : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) =
      a * DirichletHecke.uniformizer v := by
    rw [ha]; simp
  have key : ((localChar (DirichletHecke.heckeCharacter χ) v (unifUnit (Qv v)) : ℂˣ) : ℂ) =
      ((DirichletHecke.heckeCharacter χ (IdeleClassGroup.mk ℚ
        (IdeleGroup.finiteEmbedding v (a * DirichletHecke.uniformizer v))) : Circle) : ℂ) := by
    rw [← hπ]; rfl
  rw [key, map_mul, map_mul, map_mul, Circle.coe_mul, htriv, hunif]
  simp

theorem e1 : E1 := by
  unfold E1
  intro c hc M₀ hM₀
  obtain ⟨N, hN, χ, -, hχ⟩ := DirichletHecke.exists_heckeCharacter_eq hc
  haveI : NeZero (N * M₀) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Nat.pos_iff_ne_zero.mp hM₀)⟩
  refine ⟨N * M₀, inferInstance, DirichletCharacter.changeLevel (dvd_mul_right N M₀) χ,
    dvd_mul_left M₀ N, ?_⟩
  intro v hv
  rw [pOf_eq_prime] at hv ⊢
  rw [coe_localChar_unifUnit _ v hv, DirichletHecke.heckeCharacter_changeLevel, hχ]

end GlobalTheory.CompanionTheory.HalfIntegral
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodizationIntegralUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Lattice

theorem tsum_setIntegral_sub_rat : ∀ (D : D7) (m r : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r)), IsCovolOne (ratMx D m r) μr 𝓕r →
    ∀ f : Mx D m r → ℂ, Continuous f → ∀ B : ℝ≥0, (∀ y, ∑' p : Matrix (Fin m) (Fin r) D.host.E, ‖f (y - rat p)‖ₑ ≤ B) →
      Integrable f μr ∧ ∑' p : Matrix (Fin m) (Fin r) D.host.E, ∫ y in 𝓕r, f (y - rat p) ∂μr = ∫ t, f t ∂μr := by
  intro D m r μr 𝓕r h f hf B hB
  obtain ⟨hHaar, hFD, hvol⟩ := h
  haveI := hHaar
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : Countable D.host.E :=
    Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin m) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin m → Fin r → D.host.E))
  have hinc : Function.Injective (Formalism.L2.Theta.incA D) := by
    have h0 : Function.Injective (algebraMap ↥D.host.F (AF ↥D.host.F)) :=
      NumberField.AdeleRing.algebraMap_injective _ _
    exact Algebra.TensorProduct.includeRight_injective h0
  have hmem : ∀ p : Matrix (Fin m) (Fin r) D.host.E, rat p ∈ ratMx D m r :=
    fun p => AddMonoidHom.mem_range.mpr ⟨p, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Matrix (Fin m) (Fin r) D.host.E ≃ ratMx D m r,
      ∀ p, ((e p : ratMx D m r) : Mx D m r) = rat p := by
    refine ⟨Equiv.ofBijective (fun p => ⟨rat p, hmem p⟩) ⟨fun p q hpq => ?_, fun g => ?_⟩, fun p => rfl⟩
    · have h2 : p.map (Formalism.L2.Theta.incA D) = q.map (Formalism.L2.Theta.incA D) :=
        congrArg Subtype.val hpq
      exact Matrix.map_injective hinc h2
    · obtain ⟨p, hp⟩ := AddMonoidHom.mem_range.mp g.2
      exact ⟨p, Subtype.ext hp⟩
  haveI : Countable (ratMx D m r) := Countable.of_equiv _ e
  haveI : VAddInvariantMeasure (ratMx D m r) (Mx D m r) μr :=
    ⟨fun c s _ => measure_preimage_add μr (c : Mx D m r) s⟩
  have hv : ∀ (p : Matrix (Fin m) (Fin r) D.host.E) (x : Mx D m r), -(e p) +ᵥ x = x - rat p := by
    intro p x
    change ((-(e p) : ratMx D m r) : Mx D m r) + x = x - rat p
    rw [AddSubgroup.coe_neg, he]
    exact neg_add_eq_sub (rat p) x
  have hmeas : ∀ p : Matrix (Fin m) (Fin r) D.host.E, Measurable (fun x => ‖f (x - rat p)‖ₑ) :=
    fun p => (hf.comp (continuous_id.sub continuous_const)).measurable.enorm
  have hlin : ∫⁻ x, ‖f x‖ₑ ∂μr ≤ B := by
    rw [hFD.lintegral_eq_tsum', ← e.tsum_eq]
    simp_rw [hv]
    rw [← lintegral_tsum (fun p => (hmeas p).aemeasurable)]
    calc ∫⁻ x in 𝓕r, ∑' p, ‖f (x - rat p)‖ₑ ∂μr ≤ ∫⁻ _ in 𝓕r, (B : ℝ≥0∞) ∂μr :=
          lintegral_mono fun x => hB x
      _ = B := by rw [lintegral_const, Measure.restrict_apply_univ, hvol, mul_one]
  have hint : Integrable f μr := ⟨hf.aestronglyMeasurable, lt_of_le_of_lt hlin ENNReal.coe_lt_top⟩
  refine ⟨hint, ?_⟩
  rw [hFD.integral_eq_tsum' f hint, ← e.tsum_eq]
  simp_rw [hv]

end GlobalTheory.CompanionTheory.EisUnfold.Lattice
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectivePointChartRatio
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem ptP_mem_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c) :=
  CxPts.ofHom_mem _ _ _

theorem ev_ptP (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (a : Γ(PSpace ℤ N, chart ℤ N c)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) a (ptP N c w) = chartHom N c w a :=
  CxPts.ev_ofHom _ _ _ a

theorem ev_ptP_ratio (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c) (ratio ℤ N c i) (ptP N c w) = w i / w c := by
  rw [ev_ptP]
  by_cases h : i = c
  · subst h
    rw [ratio, ratioOn_self, map_one, div_self hc]
  · have e : (chartAlgEquiv ℤ N c).symm (ratio ℤ N c i) = X ⟨i, h⟩ := by
      rw [← chartAlgEquiv_X ℤ N c ⟨i, h⟩]
      exact AlgEquiv.symm_apply_apply _ _
    simp [chartHom, e]

theorem ptP_mem_chart_iff (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0)
    (i : Fin (N + 1)) :
    ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0 := by
  have e := CxPts.mem_ptsIn_basicOpen (ptP_mem_chart N c w) (ratio ℤ N c i)
  rw [ratio, basicOpen_ratioOn, CxPts.mem_ptsIn_inf] at e
  rw [← ratio, ev_ptP_ratio N c w hc i] at e
  constructor
  · intro h
    have := e.1 ⟨ptP_mem_chart N c w, h⟩
    exact fun h0 => this (by rw [h0, zero_div])
  · intro h
    exact (e.2 (div_ne_zero h hc)).2

theorem ptP_chart (N : ℕ) (c : Fin (N + 1)) (w : Fin (N + 1) → ℂ) (hc : w c ≠ 0) :
    (∀ i, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) ↔ w i ≠ 0) ∧
    ∀ i j, GlobalTheory.CompanionTheory.MPSmooth.ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N i) →
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (GlobalTheory.CompanionTheory.MPSmooth.ptP N c w) =
        w j / w i := by
  refine ⟨ptP_mem_chart_iff N c w hc, fun i j hi => ?_⟩
  have hwi : w i ≠ 0 := (ptP_mem_chart_iff N c w hc i).1 hi
  have hW : ptP N c w ∈ ptsIn (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i) :=
    CxPts.mem_ptsIn_inf.2 ⟨ptP_mem_chart N c w, hi⟩
  have h₁ : ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left i *
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j =
      ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left j :=
    ratioOn_mul_ratioOn
  have h₂ := congrArg (fun f => CxPts.ev (PSpace.str ℤ N) σ₀ _ f (ptP N c w)) h₁
  simp only [CxPts.ev_mul] at h₂
  have ea : ∀ k, CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) c inf_le_left k) (ptP N c w) = w k / w c := fun k =>
    (CxPts.ev_res inf_le_left hW (ratio ℤ N c k)).trans (ev_ptP_ratio N c w hc k)
  have eb : CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N c ⊓ chart ℤ N i)
      (ratioOn (chart ℤ N c ⊓ chart ℤ N i) i inf_le_right j) (ptP N c w) =
      CxPts.ev (PSpace.str ℤ N) σ₀ (chart ℤ N i) (ratio ℤ N i j) (ptP N c w) :=
    CxPts.ev_res inf_le_right hW (ratio ℤ N i j)
  rw [ea, ea, eb] at h₂
  field_simp at h₂ ⊢
  exact h₂

end GlobalTheory.CompanionTheory.MPSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneFreeFibreLocal
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.LengthFibre

open GlobalTheory.CompanionTheory.SW.FibreRatio

theorem isFibreFamily_field {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) (h : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hm : IsGramFibFree R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam 1 M)
      (fun X : Fin 1 → Fin M → R ⊗[F] E =>
        algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) id
      {X : Fin 1 → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} lam Set.univ
      (fun s => m (hermScal R σ s)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := hT2
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  obtain ⟨hc1, hc2, hc3⟩ := hm
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R
  have hcq : Continuous (qS R σ (F := F) (E := E)) := continuous_qS R htr
  have hmap : coordHerm R σ b lam 1 = lam.map (hermScal R σ) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hcs.measurable hA, ← coordHerm_qS R h htr b lam (hcs.measurable hA)]
    congr 1
    ext S
    show S ∈ A ↔ hermScal R σ (qS R σ S) ∈ A
    rw [hermScal_qS R h S]
  have hemb : MeasurableEmbedding (hermScal R σ (F := F) (E := E)) :=
    (Homeomorph.mk ⟨hermScal R σ, qS R σ, qS_hermScal R h, hermScal_qS R h⟩ hcs hcq).measurableEmbedding
  refine ⟨fun s => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · refine measure_mono_null (Set.compl_subset_compl.mpr ?_) (hc1 (hermScal R σ s))
    rintro X ⟨hX, hXU⟩
    refine ⟨?_, hXU⟩
    have e : gramR R σ J X = ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hX
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) = s
    rw [e]
    exact qS_hermScal R h s
  · rw [hc2 φ hφ, hmap, hemb.lintegral_map]
  · obtain ⟨ha, hb⟩ := hc3 φ hφc hφs hφU
    exact ⟨fun s _ => ha _ (Set.mem_univ _),
      (hb.comp hcs.continuousOn (fun _ _ => Set.mem_univ _))⟩

end GlobalTheory.CompanionTheory.WeilSiegel.Free.LengthFibre

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem isFibreFamily_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW (Fv F v) b lam 1 M) (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) id {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} lam Set.univ (fun s => m (hermScal (Fv F v) σ s)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b v lam hlam m hm
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact LengthFibre.isFibreFamily_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ b lam hlam.1 m hm

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootsEqOfDistinctValuationsStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_eq_of_distinct_valuations : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ), Function.Injective y → ∀ u u' : Fin n → L, (∀ i, ordL (u i) = y i) → (∀ i, ordL (u' i) = y i) → ∏ i, (X - C (u i)) = ∏ i, (X - C (u' i)) → u = u' := by
  first | exact @GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord | exact GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord | (intros; apply GlobalTheory.CompanionTheory.RootsDistinctVal.roots_eq_of_distinct_ord <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelCompactTranslateBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_compact_translate_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → ∀ (K : Subgroup (GAd σ J)), IsCompact (K : Set (GAd σ J)) → ∀ c : ℝ, 0 < c → ∀ (C : Set (GAd σ J)), IsCompact C → ∃ t1 : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ K, ∀ γ : GRat σ J, (p * a * k)⁻¹ * ratEmb σ J γ * (p * a * k) ∈ C → ∀ j : Fin r, t1 < t j → (∀ j' : Fin r, j'.val = j.val + 1 → t1 * t j' < t j) → (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, γ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) := by
  first | exact @GlobalTheory.CompanionTheory.FlagKey.flag_key | exact GlobalTheory.CompanionTheory.FlagKey.flag_key | (intros; apply GlobalTheory.CompanionTheory.FlagKey.flag_key <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianLiePreservesStableStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_lie_preserves_stable : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) → ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable | exact GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable | (intros; apply GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable <;> assumption)
end

