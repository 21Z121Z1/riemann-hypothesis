import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.DiscOrder

section General

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem idxN_eq_card (A B : Submodule R W) : idxN A B = Nat.card (A ⧸ B.comap A.subtype) := rfl

theorem idxN_mul {A B C : Submodule R W} (h1 : A ≤ B) (h2 : B ≤ C) :
    idxN B A * idxN C B = idxN C A :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr h1)
    ((Submodule.toAddSubgroup_le _ _).mpr h2)

theorem idxN_eq_one {A B : Submodule R W} : idxN A B = 1 ↔ A ≤ B :=
  AddSubgroup.relIndex_eq_one.trans (Submodule.toAddSubgroup_le _ _)

theorem exists_max_of_covBy {X Y : Submodule R W} (h : X ⋖ Y) :
    ∃ P : Ideal R, P.IsMaximal ∧ (∀ r : R, r ∈ P ↔ ∀ y ∈ Y, r • y ∈ X) ∧ idxN Y X = Nat.card (R ⧸ P) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ((covBy_iff_quot_is_simple h.le).1 h)
  refine ⟨P, hP, fun r => ⟨fun hr y hy => ?_, fun hr => ?_⟩, by rw [idxN_eq_card]; exact Nat.card_congr e.toEquiv⟩
  · have : r • (Submodule.Quotient.mk ⟨y, hy⟩ : Y ⧸ X.comap Y.subtype) = 0 := by
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective P (e (Submodule.Quotient.mk ⟨y, hy⟩))
      rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact P.mul_mem_right a hr
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    have h0 : r • e.symm (Submodule.Quotient.mk 1) = 0 := by
      rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hr y y.2
    rw [← map_smul, EmbeddingLike.map_eq_zero_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at h0
    simpa using h0

theorem exists_covBy {X Y : Submodule R W} (hY : Y.FG) (h : X < Y) : ∃ Z, X ≤ Z ∧ Z ⋖ Y := by
  have := CompleteLattice.Iic_coatomic_of_compact_element ((Submodule.fg_iff_compact Y).1 hY)
  rcases eq_top_or_exists_le_coatom (⟨X, h.le⟩ : Set.Iic Y) with e | ⟨Z, hZ, hle⟩
  · exact absurd (congrArg Subtype.val e) h.ne
  · exact ⟨Z.1, hle, (covBy_iff_coatom_Iic Z.2).2 hZ⟩

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in

theorem idxN_ne_zero {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X) (hY : Y.FG) :
    idxN Y X ≠ 0 := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom (nonZeroDivisors (𝓞 K)) Y X hY
    (by rw [indexBasic_locS_top (K := K) X hX.span_eq_top]; exact le_top)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
  have : Module.Finite (𝓞 K) Y := Module.Finite.iff_fg.mpr hY
  have : Module.Finite ℤ (Y ⧸ X.comap Y.subtype) := Module.Finite.trans (𝓞 K) _
  have : Finite (Y ⧸ X.comap Y.subtype) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (X.comap Y.subtype) q
    refine ⟨⟨(Ideal.absNorm (Ideal.span {d}) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • Submodule.mkQ (X.comap Y.subtype) y = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • (y : V) ∈ X
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← hc, mul_smul]
    exact X.smul_mem c (hdY y y.2)
  rw [idxN_eq_card]
  exact Nat.card_pos.ne'

omit [StarRing K] [FiniteDimensional K V] in
theorem lattice_between {X Y Z : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X)
    (hY : Submodule.IsLattice K Y) (h1 : X ≤ Z) (h2 : Z ≤ Y) : Submodule.IsLattice K Z :=
  Submodule.IsLattice.of_le_of_isLattice_of_fg K h1 (hY.fg.of_le h2)

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn

theorem dual_covBy {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X)
    (hY : Submodule.IsLattice K Y) (hc : X ⋖ Y) : dual h Y ⋖ dual h X := by
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  refine ⟨lt_of_le_of_ne (an _ _ hc.le) fun e => hc.ne ?_, fun Z h1 h2 => ?_⟩
  · rw [← (dl X hX).2.1, ← e, (dl Y hY).2.1]
  · have hZ := lattice_between (dl Y hY).1 (dl X hX).1 h1.le h2.le
    have a1 := an _ _ h1.le
    have a2 := an _ _ h2.le
    rw [(dl Y hY).2.1] at a1
    rw [(dl X hX).2.1] at a2
    rcases hc.eq_or_eq a2 a1 with e | e
    · exact h2.ne (by rw [← e, (dl Z hZ).2.1])
    · exact h1.ne (by rw [← e, (dl Z hZ).2.1])

theorem idxN_dual_of_covBy {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X)
    (hY : Submodule.IsLattice K Y) (hc : X ⋖ Y) : idxN (dual h X) (dual h Y) = idxN Y X := by
  obtain ⟨P, hP, hPm, hPi⟩ := exists_max_of_covBy hc
  obtain ⟨Q, hQ, hQm, hQi⟩ := exists_max_of_covBy (dual_covBy h hs hn hX hY hc)
  set σ := locBasic_sigma (genusCovol_hinj (K := K)) star_algebraMap_ringOfIntegers_mem_range with hσ
  have hσσ : ∀ r, σ (σ r) = r := fun r => genusCovol_hinj (by
    rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])
  let e : 𝓞 K ≃+* 𝓞 K := RingEquiv.ofBijective σ (Function.Involutive.bijective hσσ)
  have hle : P ≤ Q.comap σ := by
    intro r hr
    rw [Ideal.mem_comap, hQm]
    intro x hx
    rw [dualBasic_mem_dual] at hx ⊢
    intro y hy
    have := hx _ ((hPm r).1 hr y hy)
    rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range] at this
    rw [genusBasic_hsmul_right]
    exact this
  have hPQ : P = Q.comap σ := hP.eq_of_le (Ideal.comap_ne_top σ hQ.ne_top) hle
  have hm : Q = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [hPQ]
    exact (Ideal.map_comap_of_surjective σ e.surjective Q).symm
  rw [hPi, hQi]
  exact (Nat.card_congr (Ideal.quotientEquiv P Q e hm).toEquiv).symm

theorem idxN_dual {X : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X) : ∀ (n : ℕ)
    (Y : Submodule (𝓞 K) V), Submodule.IsLattice K Y → X ≤ Y → idxN Y X = n →
    idxN (dual h X) (dual h Y) = n := by
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hY hle hi
  rcases hle.eq_or_lt with rfl | hlt
  · rw [← hi, idxN_eq_one.2 le_rfl, idxN_eq_one.2 le_rfl]
  obtain ⟨Z, hXZ, hc⟩ := exists_covBy hY.fg hlt
  have hZ := lattice_between hX hY hXZ hc.le
  have m1 := idxN_mul hXZ hc.le
  have n1 := idxN_ne_zero hX hZ.fg
  have n2 := idxN_ne_zero hZ hY.fg
  have n3 : idxN Y Z ≠ 1 := fun e => hc.lt.not_ge (idxN_eq_one.1 e)
  have hlt' : idxN Z X < n := by
    rw [← hi, ← m1]
    exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero n1) (by omega)
  rw [← idxN_mul (an _ _ hc.le) (an _ _ hXZ), ih _ hlt' Z hZ hXZ rfl, idxN_dual_of_covBy h hs hn hZ hY hc,
    ← hi, ← m1, mul_comm]

end GlobalTheory.Mass.DiscOrder

namespace GlobalTheory.Mass.DiscOrder

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → discN h M ≠ 0 ∧ (discN h M = 1 ↔ IsUnimodular h M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → idxN M' M ≠ 0 ∧ discN h M = discN h M' * idxN M' M ^ 2) ∧ (∀ N ∈ genus h M, IsIntLat h N ∧ discN h N = discN h M) ∧ (∀ P : Ideal (𝓞 K), P.IsMaximal → ((discN h M : ℕ) : 𝓞 K) ∉ P → IsUnimodularAt h P M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P M → loc (K := K) P M = loc (K := K) P M') := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hn M hM
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨an, -, -, hint, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have hMd := (hint M).1 hM.2
  have h0 : ∀ N, IsIntLat h N → discN h N ≠ 0 := fun N hN => idxN_ne_zero hN.1 (dl N hN.1).1.fg
  refine ⟨h0 M hM, ?_, fun M' hM' hle => ⟨idxN_ne_zero hM.1 hM'.1.fg, ?_⟩, fun N hN => ?_,
    fun P hP hd => ?_, fun M' hM' hle P hP hu => ?_⟩
  · rw [huni, discN, idxN_eq_one]
    exact ⟨fun e => ⟨hM.2, e⟩, fun e => e.2⟩
  · have hMd' := (hint M').1 hM'.2
    rw [discN, discN, ← idxN_mul (hle.trans hMd') (an _ _ hle), ← idxN_mul hle hMd',
      idxN_dual h hs hn hM.1 _ M' hM'.1 hle rfl]
    ring
  · have hNi : IsIntLat h N := ⟨hN.1,
      (((genusBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).2.2 M N hM.1.fg hN.1.fg hN.2).2).1 hM.2⟩
    refine ⟨hNi, genusCovol_lemmaS _ M (dual h M) N (dual h N) hMd ((hint N).1 hNi.2) rfl (h0 M hM)
      (h0 N hNi) fun P hP => ?_⟩
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    have hle := locBasic_hcompl_le (K := K) P
    have key : ∀ A B : Submodule (𝓞 K) V, gmap g (loc (K := K) P A) = loc (K := K) P B →
        gmap g (locS P.primeCompl A) = locS P.primeCompl B := by
      intro A B e
      rw [← genusCovol_locS_locS hle A, gmap_locS_comm]
      change locS P.primeCompl (gmap g (loc (K := K) P A)) = _
      rw [e]
      exact genusCovol_locS_locS hle B
    obtain ⟨a1, a2, -, -, a5⟩ := isomAct (𝓞 K) K V h g hg M
    have b1 := (ld (gmap g M) (a5.2 hM.1).fg).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    refine ⟨_, g.injective, genusCovol_addData g _ _ (key _ _ hgL), genusCovol_addData g _ _ (key _ _ ?_)⟩
    rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h M)).2.1 P]
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1]
    refine le_antisymm ((locBasic_locS_mono _ fun x hx => ?_).trans (locBasic_locS_idem _ M).le)
      (locBasic_locS_mono _ hMd)
    refine ⟨(discN h M : 𝓞 K), Submonoid.subset_closure ⟨hd, fun t ht => ?_⟩, ?_⟩
    · have : t = (discN h M : 𝓞 K) := genusCovol_hinj (by rw [ht]; simp)
      rwa [this]
    · rw [Nat.cast_smul_eq_nsmul]
      have := AddSubgroup.nsmul_index_mem (H := M.toAddSubgroup.addSubgroupOf (dual h M).toAddSubgroup) ⟨x, hx⟩
      exact this
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1] at hu
    refine le_antisymm (locBasic_locS_mono _ hle) ?_
    rw [← hu]
    exact locBasic_locS_mono _ (((hint M').1 hM'.2).trans (an _ _ hle))

end GlobalTheory.Mass.DiscOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermSplitsUnimodularComplement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.UnimodSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem eq_zero_of_forall_hf (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    (hd : IsUnit Hm.det) {z : Fin n → E} (hz : ∀ v, hf L Hm z v = 0) : z = 0 := by
  have h1 : Matrix.vecMul z Hm = 0 := by
    funext j
    have := hz (Pi.single j 1)
    simp only [hf, Pi.single_apply, apply_ite (⇑L.cj), map_one, map_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have := congrArg (fun u => Matrix.vecMul u Hm⁻¹) h1
  simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hd] using this

omit [IsNonarchimedeanLocalField F] [CharZero F] in

theorem cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem hf_add_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem hf_add_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    hf L Hm x (y + y') = hf L Hm x y + hf L Hm x y' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem hf_sum_right {L : LocE F E} {r k : ℕ} (S : Frames L r k) {ι : Type} [Fintype ι] (x : S.V)
    (c : ι → E) (g : ι → S.V) :
    hf L S.Hm x (∑ l, c l • g l) = ∑ l, hf L S.Hm x (g l) * L.cj (c l) := by
  rw [FrameBasic.hf_conj L S.herm.1 x, UnimodTerm.hf_sum_left S, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← FrameBasic.hf_conj L S.herm.1 x (g l)]

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ b : Fin (k - 1) → S.V, (∀ i, b i ∈ S.W0) ∧ Λ = S.M d Λ ⊔ Submodule.span L.O (Set.range b) ∧ (∀ i j, hf L S.Hm (b i) (b j) ∈ L.O) ∧ ∃ P : Matrix (Fin (k - 1)) (Fin (k - 1)) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (b i) (b j)) * P = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha
  obtain ⟨hSD, hW, hM, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, hc, -⟩ := FrameBasic.main L r k S
  obtain ⟨-, -, -, hW0, -, b, hbli, hb⟩ := Gluing.main L r k S d Λ hT
  have hMΛ : ∀ m ∈ S.M d Λ, m ∈ Λ := fun m h => (hM h).1
  have hMME : ∀ m ∈ S.M d Λ, m ∈ S.ME := fun m h => (hM h).2
  have hbL : ∀ w, w ∈ Submodule.span L.O (Set.range b) ↔ w ∈ S.complementLatticeOfDatum d := fun w => by
    rw [hb]; rfl
  have hbW : ∀ i, b i ∈ S.W0 := fun i => ((hbL _).1 (Submodule.subset_span ⟨i, rfl⟩)).1
  have hspan : ∀ w ∈ S.W0, (w ∈ Λ ↔ w ∈ Submodule.span L.O (Set.range b)) := by
    intro w hw
    rw [hbL]
    constructor
    · intro h; exact ((hW0 w hw).1 h).1
    · intro h; exact (UnimodTerm.mem_iff_graph S hT ha hw).2 h.2.2.2
  have hdec : ∀ x, ∃ m ∈ S.ME, ∃ w ∈ S.W0, x = m + w := by
    intro x
    have hx : x ∈ S.ME ⊔ S.W0 := by rw [hc.sup_eq_top]; trivial
    obtain ⟨m, hm, w, hw, h⟩ := Submodule.mem_sup.1 hx
    exact ⟨m, hm, w, hw, h.symm⟩
  have hΛ : Λ = S.M d Λ ⊔ Submodule.span L.O (Set.range b) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨m, hm, w, hw, rfl⟩ := hdec x
      have h1 : m ∈ S.M d Λ := UnimodTerm.proj_mem S hT ha hx hm (by simpa using hw)
      have h2 : w ∈ Λ := by simpa using Λ.sub_mem hx (hMΛ m h1)
      exact Submodule.mem_sup.2 ⟨m, h1, w, (hspan w hw).1 h2, rfl⟩
    · refine sup_le (fun m h => hMΛ m h) (fun w h => ?_)
      exact (hspan w ((hbL w).1 h).1).2 h
  have hbΛ : ∀ i, b i ∈ Λ := fun i => (hspan _ (hbW i)).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hG : ∀ i j, hf L S.Hm (b i) (b j) ∈ L.O := fun i j => (hSD.2 (b j)).2 (hbΛ j) (b i) (hbΛ i)
  have hYW : Submodule.span E (Set.range b) ≤ S.W0 :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbW i)
  have hOY : ∀ w ∈ Submodule.span L.O (Set.range b), w ∈ Submodule.span E (Set.range b) :=
    fun w h => Submodule.span_le_restrictScalars L.O E (Set.range b) h
  have hWY : S.W0 ≤ Submodule.span E (Set.range b) := by
    have htop : (⊤ : Submodule E S.V) ≤ S.ME ⊔ Submodule.span E (Set.range b) := by
      rw [← hSD.1.2, Submodule.span_le]
      intro x hx
      have hx' : x ∈ S.M d Λ ⊔ Submodule.span L.O (Set.range b) := by rw [← hΛ]; exact hx
      obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
      exact Submodule.mem_sup.2 ⟨m, hMME m hm, w, hOY w hw, rfl⟩
    intro w hw
    obtain ⟨m, hm, y, hy, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := w)))
    have hm0 : m ∈ S.ME ⊓ S.W0 := ⟨hm, by simpa using S.W0.sub_mem hw (hYW hy)⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at hm0
    rw [hm0, zero_add]; exact hy
  have hzero : ∀ z ∈ S.W0, (∀ j, hf L S.Hm z (b j) = 0) → z = 0 := by
    intro z hz hzb
    apply eq_zero_of_forall_hf L S.herm.2
    intro v
    obtain ⟨m, hm, w, hw, rfl⟩ := hdec v
    have e1 : hf L S.Hm z m = 0 := hz m hm
    have e2 : hf L S.Hm z w = 0 := by
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (hWY hw)
      rw [hf_sum_right S]
      simp [hzb]
    rw [hf_add_right, e1, e2, add_zero]
  set Gb : Matrix (Fin (k - 1)) (Fin (k - 1)) E := Matrix.of fun i j => hf L S.Hm (b i) (b j) with hGb
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hunit : IsUnit Gb := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    have hinj : Function.Injective Gb.vecMulLinear := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      have hz : ∑ i, c i • b i = 0 := by
        apply hzero _ (S.W0.sum_mem fun i _ => S.W0.smul_mem _ (hbW i))
        intro j
        have := congrFun hc j
        simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Pi.zero_apply, hGb,
          Matrix.of_apply] at this
        rw [UnimodTerm.hf_sum_left S, ← this]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      funext i
      exact Fintype.linearIndependent_iff.1 hbli c hz i
    exact IsArtinian.surjective_of_injective_endomorphism Gb.vecMulLinear hinj
  have hdet := (Matrix.isUnit_iff_isUnit_det Gb).1 hunit
  have hGP : Gb * Gb⁻¹ = 1 := Matrix.mul_nonsing_inv Gb hdet
  refine ⟨b, hbW, hΛ, hG, Gb⁻¹, ?_, hGP⟩
  intro l j
  set y : S.V := ∑ l', L.cj (Gb⁻¹ l' j) • b l' with hy
  have hyb : ∀ i, hf L S.Hm (b i) y = if i = j then 1 else 0 := by
    intro i
    rw [hy, hf_sum_right S]
    have := congrFun (congrFun hGP i) j
    simp only [Matrix.mul_apply, Matrix.one_apply, hGb, Matrix.of_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun l' _ => by rw [L.cj_cj]
  have hyW : y ∈ S.W0 := S.W0.sum_mem fun l' _ => S.W0.smul_mem _ (hbW l')
  have hyΛ : y ∈ Λ := by
    refine (hSD.2 y).1 fun x hx => ?_
    have hx' : x ∈ S.M d Λ ⊔ Submodule.span L.O (Set.range b) := by rw [← hΛ]; exact hx
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    obtain ⟨o, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hw
    have e1 : hf L S.Hm m y = 0 := by
      rw [FrameBasic.hf_conj L S.herm.1 m y, hyW m (hMME m hm), map_zero]
    have e2 : ∑ i, o i • b i = ∑ i, (o i : E) • b i := rfl
    rw [hf_add_left, e1, zero_add, e2, UnimodTerm.hf_sum_left S]
    simp only [hyb, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (o j).2
  obtain ⟨Q, hQ⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 ((hspan y hyW).1 hyΛ)
  have hQ' : ∑ i, (Q i : E) • b i = y := hQ
  have hcoef : L.cj (Gb⁻¹ l j) = (Q l : E) := by
    have h0 := Fintype.linearIndependent_iff.1 hbli (fun l' => L.cj (Gb⁻¹ l' j) - (Q l' : E)) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hy, hQ', sub_self])
    exact sub_eq_zero.1 (h0 l)
  have h1 := cj_mem L (Q l).2
  rw [← hcoef, L.cj_cj] at h1
  exact h1

end GlobalTheory.HL.UnimodSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InclEIntMem
section
open NumberField
open scoped TensorProduct

noncomputable section
open Classical

namespace GlobalTheory.VectorInclusion

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def vecIncl (x : Fin n → E) : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F :=
  fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (x i)

theorem inclE_int_mem (c : 𝓞 E) :
    Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E) ∈ Formalism.MainNotions.S.IntAf F E := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨(c : E), ⟨c, rfl⟩⟩, ?_⟩
  rfl

theorem vecIncl_add (x y : Fin n → E) :
    vecIncl (F := F) (x + y) = vecIncl (F := F) x + vecIncl (F := F) y := by
  funext i; simp [vecIncl, map_add]

theorem vecIncl_zero : vecIncl (F := F) (0 : Fin n → E) = 0 := by
  funext i; simp [vecIncl]

theorem vecIncl_smul (c : 𝓞 E) (x : Fin n → E) :
    vecIncl (F := F) (c • x) =
      (⟨Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E), inclE_int_mem c⟩ : Formalism.MainNotions.S.IntAf F E) •
        vecIncl (F := F) x := by
  funext i
  simp only [vecIncl, Pi.smul_apply]
  rw [Algebra.smul_def, map_mul]
  rfl

theorem lamAf_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) := by
  obtain ⟨s, hs⟩ := hL
  refine ⟨s.image (vecIncl (F := F)), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    have hxL : x ∈ L := hs ▸ Submodule.subset_span hx
    exact ⟨⟨x, hxL⟩, rfl⟩
  · unfold Formalism.MainNotions.S.lamAf
    rw [Submodule.span_le]
    rintro y ⟨⟨x, hx⟩, rfl⟩
    have key : ∀ z ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)),
        vecIncl (F := F) z ∈ Submodule.span (Formalism.MainNotions.S.IntAf F E)
          ((s.image (vecIncl (F := F)) : Finset _) : Set (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        apply Submodule.subset_span
        simp only [Finset.coe_image]
        exact ⟨z, hz, rfl⟩
      | zero => rw [vecIncl_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [vecIncl_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [vecIncl_smul]; exact Submodule.smul_mem _ _ ha
    rw [← hs] at hx
    exact key x hx

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.FG L → Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) :=
  fun L hL => lamAf_fg L hL

end GlobalTheory.VectorInclusion

end
end

