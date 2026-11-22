import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0096
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Formalism.LocalToGlobal.Columns.Bundle0015
import Formalism.LocalToGlobal.Columns.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.HasDSComp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FlatHermitianReps.AdmissibleRepresentationFactorisation
import Mathlib.LinearAlgebra.Lagrange
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.UnitarySiegelSets.SiegelSetUnitaryHolds
import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.RegClassIntHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProof
section
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.BasicNotions MvPolynomial
open scoped Matrix

namespace GlobalTheory.NabBC

variable {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K]

theorem mem_localization_of_mem' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {L : Submodule R W} {x : W} (h : x ∈ L) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L :=
  show ∃ s ∈ p.primeCompl, s • x ∈ L from ⟨1, p.primeCompl.one_mem, by rw [one_smul]; exact h⟩

abbrev vmap {n : ℕ} (f : K₀ →+* K) (x : Fin n → K₀) : Fin n → K := fun a => f (x a)

theorem vmap_add {n : ℕ} (f : K₀ →+* K) (x y : Fin n → K₀) : vmap f (x + y) = vmap f x + vmap f y := by
  funext a; simp [vmap]

theorem vmap_smul {n : ℕ} (f : K₀ →+* K) (r : 𝓞 K₀) (x : Fin n → K₀) :
    vmap f (r • x) = RingOfIntegers.mapRingHom f r • vmap f x := by
  funext a
  change f ((r : K₀) * x a) = ((RingOfIntegers.mapRingHom f r : 𝓞 K) : K) * f (x a)
  rw [map_mul]
  rfl

theorem span_image_span {n : ℕ} (f : K₀ →+* K) (S : Set (Fin n → K₀)) :
    Submodule.span (𝓞 K) (vmap f '' (Submodule.span (𝓞 K₀) S : Set (Fin n → K₀))) =
      Submodule.span (𝓞 K) (vmap f '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      have : vmap f (0 : Fin n → K₀) = 0 := by funext a; simp [vmap]
      rw [this]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [vmap_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [vmap_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem localization_span_image_le {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {A B : Submodule (𝓞 K₀) (Fin n → K₀)} (h : A ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀)))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
  have key : Submodule.span (𝓞 K) (vmap f '' (A : Set (Fin n → K₀))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (vmap f '' (B : Set (Fin n → K₀)))) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨t, ht, hta⟩ := h ha
    exact show ∃ s ∈ w.asIdeal.primeCompl, s • vmap f a ∈ _ from
      ⟨RingOfIntegers.mapRingHom f t, hw t ht, by rw [← vmap_smul]; exact Submodule.subset_span ⟨_, hta, rfl⟩⟩
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := key hsx
  exact show ∃ u ∈ w.asIdeal.primeCompl, u • x ∈ _ from
    ⟨t * s, Submonoid.mul_mem _ ht hs, by rw [mul_smul]; exact htx⟩

theorem span_vmap_colLat {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    Submodule.span (𝓞 K) (vmap f '' (colLat C : Set (Fin n → K₀))) = colLat (Formalism.UG.bc f C) := by
  unfold colLat
  rw [span_image_span, ← Set.range_comp]
  congr 1

theorem isBasisAt_span_vmap {n : ℕ} (f : K₀ →+* K) (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    {L : Submodule (𝓞 K₀) (Fin n → K₀)} {C : GL (Fin n) K₀} (hC : IsBasisAt w₀ L C) :
    IsBasisAt w (Submodule.span (𝓞 K) (vmap f '' (L : Set (Fin n → K₀)))) (Formalism.UG.bc f C) := by
  unfold IsBasisAt at hC ⊢
  rw [← span_vmap_colLat]
  have h1 : L ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (colLat C) := hC ▸ fun x hx => mem_localization_of_mem' _ hx
  have h2 : colLat C ≤ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal L := hC.symm ▸ fun x hx => mem_localization_of_mem' _ hx
  exact le_antisymm (localization_span_image_le f w₀ w hw h1) (localization_span_image_le f w₀ w hw h2)

theorem tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K) (emb : ι → E →+* K₀) (τ : ι)
    (M : Submodule (𝓞 E) (Fin n → E)) :
    tauLat (fun τ => f.comp (emb τ)) τ M = Submodule.span (𝓞 K) (vmap f '' (tauLat emb τ M : Set (Fin n → K₀))) := by
  unfold tauLat
  rw [span_image_span, Set.image_image]
  rfl

theorem invTr_bc {n : ℕ} (f : K₀ →+* K) (C : GL (Fin n) K₀) :
    inside₂ K n (Formalism.UG.bc f C) = Formalism.UG.bc f (inside₂ K₀ n C) := by
  apply Units.ext
  change (((Formalism.UG.bc f C)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
    ((Formalism.UG.bc f (inside₂ K₀ n C) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [← map_inv, bc_coe, bc_coe, ← Matrix.transpose_map]
  rfl

theorem isBasisAt_dualFr_tauLat_comp {E ι : Type} [Field E] [NumberField E] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (τ : ι) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M)
    (w₀ : HeightOneSpectrum (𝓞 K₀)) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal)
    (C : GL (Fin n) K₀) (hC : IsBasisAt w₀ (tauLat emb τ M) C) :
    IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (inside₂ K₀ n C)) := by
  rw [← invTr_bc]
  refine GlobalTheory.DualWeylDual.isBasisAt_dualFr w (tauLatLattice E K ι n _ τ M hM).fg ?_
  rw [tauLat_comp]
  exact isBasisAt_span_vmap f w₀ w hw hC

theorem nabStd_le_span_map {ι : Type} [Fintype ι] {n : ℕ} (f : K₀ →+* K) (lam : ι → DomWeight n) :
    nabStd K lam ≤ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) := by
  have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
  have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
  rw [h1, ← h2]
  intro x hx
  exact Submodule.subset_span ⟨x, hx, MvPolynomial.map_id x⟩

theorem map_smul_int {σ : Type} (f : K₀ →+* K) (t : 𝓞 K₀) (P : MvPolynomial σ K₀) :
    RingOfIntegers.mapRingHom f t • MvPolynomial.map f P = MvPolynomial.map f (t • P) := by
  ext m
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map]
  change ((RingOfIntegers.mapRingHom f t : 𝓞 K) : K) * f (P.coeff m) = f ((t : K₀) * P.coeff m)
  rw [map_mul]
  rfl

theorem mem_localization_span_map {E ι : Type} [Field E] [NumberField E] [Fintype ι] {n : ℕ} (f : K₀ →+* K)
    (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M)
    (w : HeightOneSpectrum (𝓞 K)) {F : Pol K ι n}
    (hF : F ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :
    F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)))) := by
  classical
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  set N' := Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) with hN'
  have key : ∀ H ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))),
      actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) H ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' := by
    intro H hH
    refine (Submodule.span_le (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N').comap
      ((actP lam (fun τ => Formalism.UG.bc f (B₀ τ))).restrictScalars (𝓞 K)))).2 ?_ hH
    rintro _ ⟨g, hg, rfl⟩
    show actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N'
    rw [← GlobalTheory.ValCmp.use₂]
    have hg' : actP lam B₀ g ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) := by
      rw [L0]
      exact Submodule.mem_map_of_mem (mem_localization_of_mem' _ hg)
    obtain ⟨t, ht, htg⟩ := hg'
    refine ⟨RingOfIntegers.mapRingHom f t, hw t ht, ?_⟩
    have e := map_smul_int f t (actP lam B₀ g)
    refine (congrArg (· ∈ N') e).mpr ?_
    exact Submodule.subset_span ⟨_, htg, rfl⟩
  have hF' : F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) :=
    mem_localization_of_mem' _ hF
  rw [L1] at hF'
  obtain ⟨G, ⟨s, hs, hsG⟩, rfl⟩ := hF'
  obtain ⟨t, ht, htG⟩ := key _ (nabStd_le_span_map f lam hsG)
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  convert htG using 1
  rw [mul_smul]
  congr 1
  exact (((actP lam fun τ => Formalism.UG.bc f (B₀ τ)).restrictScalars (𝓞 K)).map_smul s G).symm

theorem nabBaseChange : GlobalTheory.BaseCmp.NabBaseChange := by
  intro E K₀ K ι _ _ _ _ _ _ _ n f emb lam M hM F hF
  obtain ⟨-, -, hV⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hP : (F : Pol K ι n) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f ''
      (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n))) :=
    GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => GlobalTheory.NabBC.mem_localization_span_map f emb lam M hM w hF
  have hS : ((VV K lam).subtype.restrictScalars (𝓞 K)) ''
      {y : VV K lam | ∃ x ∈ nabAtr emb lam M, (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)} =
      MvPolynomial.map f '' (nabP lam fun τ => dualFr (tauLat emb τ M) : Set (Pol K₀ ι n)) := by
    ext P
    constructor
    · rintro ⟨y, ⟨x, hx, hxy⟩, rfl⟩
      exact ⟨x.1, hx, hxy.symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hxV : x ∈ VV K₀ lam := hV K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) x hx
      exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam x hxV⟩, ⟨⟨x, hxV⟩, hx, rfl⟩, rfl⟩
  rw [← hS, ← Submodule.map_span] at hP
  obtain ⟨y, hy, hyF⟩ := hP
  have e : y = F := Subtype.ext hyF
  rwa [← e]

end GlobalTheory.NabBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllTraceOfMiddleX
section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp GlobalTheory.ArchVanish
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PsCo.Plug
open MainStatements.WeightKernel
set_option maxHeartbeats 1000000 in

theorem hyperX : CuspAny → ArchZero → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → HyperZeroX := by
  intro hCA hAZ hRS D V lam S M T U μa μf μ _ _ fa ff hTD γ hreg hirr hna
  obtain ⟨Φ, L, a, hgood⟩ := exists_isGood V
  obtain ⟨g, P, hpar, hne, hmem⟩ := GlobalTheory.T.exists_conj_mem_standardLevi_of_reducible_charpoly hTD.1.pos hRS Φ γ hreg hirr hna
  refine GlobalTheory.SplitTorusZero.zeroClause_of_conj μ _ γ g ?_
  set γ0 := g * γ * g⁻¹ with hγ0
  have hreg0 : IsRegSS γ0.1.1 := by
    show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)
    unfold IsRegSS
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact hreg
  obtain ⟨hodd, -, -, hNF, hRP, hA, hF⟩ := hTD
  have hff := hF.isFinFamily
  haveI : ∀ w, (μa w).IsHaarMeasure := hRP.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hRP.haar_loc
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have hnc := (GlobalTheory.T.centralizer_regular_levi_commutative_noncompact D V Φ P hpar γ0 hreg0 hmem).2.2 (Finset.nonempty_iff_ne_empty.1 hne) w
  have hcm := isCMExt_host D
  have horb : ∀ (ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ0)))) [ds.IsHaarMeasure]
      [ds.IsMulRightInvariant], HasOrbInt (μa w) (projArch D.sp.cm.sig V.gram w (rat V γ0)) ds (fa w) 0 := by
    obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
    intro ds _ _
    haveI := (M.ds ρ).1
    have hs : IsRegSS (matAt V ρ (projArch D.sp.cm.sig V.gram (placeOf D ρ) (rat V γ0))) :=
      (isRegSS_archMat_iff hcm (embOverOf D ρ)).2 (isRegSS_projArch_ratEmb hreg0 _)
    exact (hA ρ).orb_noncompact _ hs hnc ds
  obtain ⟨ds, hds1, hds2⟩ : ∃ ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ0))),
      ds.IsHaarMeasure ∧ ds.IsMulRightInvariant := by
    haveI : LocallyCompactSpace (cent (projArch D.sp.cm.sig V.gram w (rat V γ0))) :=
      (isClosed_cent _).locallyCompactSpace
    exact ⟨Measure.haar, inferInstance, isMulRightInvariant_cent
      (isMulCommutative_cent_projArch_ratEmb (σ := D.sp.cm.sig) (J := V.gram) hreg0 w) _⟩
  exact hAZ D V μ fa ff hA.mem hff
    (fun fa' hfa' => hCA D V hodd T U hNF μf hRP.haar_loc ff hF fa' hfa') γ0 hreg0 w (μa w) ds (horb ds)
end GlobalTheory.PsCo.Plug
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX NoFixed)
open GlobalTheory.TrMult GlobalTheory.TruncKer
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PsCo.Plug
open MainStatements.WeightKernel
theorem hyperZero_of_intX (hI : MainStatements.RegularCuspidalTrace.RegClassInt) (hRS : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple) : HyperZeroX :=
  hyperX cuspAny (archZero bumpOn (weight (weightDiag lagr shiftT boundT))
    (vanish (kerSwap (kerUnif smoothSum closedGraph)) identOne identTwo) fdRight archGroup archUnimod hI) hRS
end GlobalTheory.PsCo.Plug
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestDataX PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPartX TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
noncomputable section
namespace GlobalTheory.PsCo.Plug
open GlobalTheory.CompanionTheory.EllTrace
open GlobalTheory.TruncKer

theorem ellTrace_of_middleX : MainStatements.RegularCuspidalTrace.RegClassInt → MainStatements.RegularCuspidalTrace.RegClassFin → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTermX → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.NonFieldTypeVanishingX → HyperZeroX → EllTraceX := by
  intro hInt hFinC hCO hPC hIw _hRS hNF hHZ D V lam S M T U μa μf μ _ _ fa ff hT
  have hT' := hT
  obtain ⟨hodd, -, -, hnf, hμ, harch, hfin⟩ := hT'
  have hμ' := hμ
  obtain ⟨hμa, hμf, -, -⟩ := hμ'
  set f := tensor D.sp.cm.sig V.gram fa ff with hfdef
  have hcc : f ∈ CcGA V := tensor_mem_ccAd harch.mem hfin.isFinFamily
  have hcs := continuous_of_mem_ccAd hcc
  obtain ⟨hH, -⟩ := GlobalTheory.T.typeHypothesis_forms_agree D V T hnf
  haveI := hμa
  haveI := hμf
  have hconst := hPC.2 D V hodd S M T hH U μa μf f ⟨fa, ff, harch, hfin, rfl⟩
  have hcusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ f :=
    hCO D V μ f hcc (fun 𝔉 h𝔉 ν hν x y => ((hconst 𝔉 h𝔉).1 ν x y).2)
      (fun 𝔉 h𝔉 ν hν x y => ((hconst 𝔉 h𝔉).2 ν x y).2)
  have hcuspFn : MainStatements.RegularCuspidalTrace.IsCuspFn f := fun 𝔉 h => (hconst 𝔉 h).1
  refine ⟨hcusp.traceClass, ?_⟩
  rw [hcusp.trace_eq_integral]
  haveI : Countable (GF V) := countable_GF V
  let ι := {𝔬 : Set (GF V) // ∃ γ : GF V, IsRegSS γ.1.1 ∧ 𝔬 = {δ | IsConj γ δ}}
  haveI : Countable ι := by
    have hs : Function.Surjective
        (fun γ : {γ : GF V // IsRegSS γ.1.1} => (⟨{δ | IsConj γ.1 δ}, γ.1, γ.2, rfl⟩ : ι)) := by
      rintro ⟨_, γ, hγ, rfl⟩
      exact ⟨⟨γ, hγ⟩, rfl⟩
    exact hs.countable
  let k : ι → GlobalTheory.AutomorphicL2Unitary.Quot (GQ V) → ℂ := fun i =>
    GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun x => ∑' δ : i.1, f (x⁻¹ * rat V δ * x))
  have hkint : ∀ i : ι, Integrable (k i) (autMeasure V μ) := by
    rintro ⟨_, γ, hγ, rfl⟩
    obtain ⟨hcl, -⟩ := (GlobalTheory.T.regularSemisimple_rational_class_kernel_integrals D V γ hγ).2 f
    have := hInt D V μ f hcc hcuspFn γ hγ
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f = fun x => ∑' δ : {δ | IsConj γ δ}, f (x⁻¹ * rat V δ * x)
      from funext hcl] at this
    exact this
  have hreg : ∀ (δ : GF V) (x : GA D V), f (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 :=
    fun δ x h => GlobalTheory.T.isRegularSemisimple_of_testFunction_ne_zero hIw D V T U μf ff hfin fa δ x h
  have hPc : ∀ a b : GF V, IsConj a b → Irreducible a.1.1.charpoly → Irreducible b.1.1.charpoly :=
    fun a b h ha => charpoly_eq_of_isConj h ▸ ha
  refine GlobalTheory.T.integral_hasSum_eq_integral_indicator_hasSum' (autMeasure V μ) k hkint ?_
    {i : ι | ∀ δ ∈ i.1, Irreducible δ.1.1.charpoly} _ _ (fun q => ?_) (fun q => ?_) ?_
  · refine ((hFinC D V f hcc).preimage Subtype.val_injective.injOn).subset fun i hi => ⟨i.2, ?_⟩
    by_contra hno
    apply hi
    have hz : ∀ q, k i q = 0 := by
      intro q
      change (∑' δ : i.1, f (q.out⁻¹ * rat V δ * q.out)) = 0
      have : ∀ δ : i.1, f (q.out⁻¹ * rat V δ * q.out) = 0 := fun δ => by
        by_contra h
        exact hno ⟨q.out, δ.1, δ.2, h⟩
      simp [this]
    simp [hz]
  · obtain ⟨hsupp, hsum⟩ := kernel_diag_hasSum V hcc q.out
    have := (GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection _ hsupp (fun δ => IsRegSS δ.1.1) (fun δ => Irreducible δ.1.1.charpoly)
      (fun δ h => hreg δ _ h) hPc).1
    rw [hsum.tsum_eq] at this
    exact this
  · obtain ⟨hsupp, -⟩ := kernel_diag_hasSum V hcc q.out
    have := (GlobalTheory.T.hasSum_conjClasses_regroup_with_invariant_selection _ hsupp (fun δ => IsRegSS δ.1.1) (fun δ => Irreducible δ.1.1.charpoly)
      (fun δ h => hreg δ _ h) hPc).2
    have hfs : (Function.support fun δ : {δ : GF V // Irreducible δ.1.1.charpoly} =>
        f (q.out⁻¹ * rat V δ.1 * q.out)).Finite :=
      (hsupp.preimage Subtype.val_injective.injOn).subset fun δ hδ => hδ
    have e : GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (ellKernel V f) q =
        ∑' δ : {δ : GF V // Irreducible δ.1.1.charpoly}, f (q.out⁻¹ * rat V δ.1 * q.out) := by
      change ellKernel V f q.out = _
      rw [ellKernel, tsum_eq_finsum hfs]
    rw [e]
    exact this
  · rintro ⟨_, γ, hγ, rfl⟩ hi
    have hirr : ¬ Irreducible γ.1.1.charpoly := fun h =>
      hi fun δ hδ => hPc γ δ hδ h
    have hZ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ZeroClause μ f (ratEmb D.sp.cm.sig V.gram γ) := by
      by_cases hA : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1
      · exact hNF.zero hodd hH hμ ⟨fa, ff, harch, hfin, rfl⟩ hA
      · exact hHZ D V lam S M T U μa μf μ fa ff hT γ hγ hirr hA
    obtain ⟨hcl, hiff⟩ := (GlobalTheory.T.regularSemisimple_rational_class_kernel_integrals D V γ hγ).2 f
    have := ((hiff hcs.1 hcs.2 μ 0).1 hZ).2
    rw [show GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f = fun x => ∑' δ : {δ | IsConj γ δ}, f (x⁻¹ * rat V δ * x)
      from funext hcl] at this
    exact this
end GlobalTheory.PsCo.Plug
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PsCo.Plug.ellipticSideDirect : GlobalTheory.Published.CuspTraceClass → EllTraceX := fun tc =>
  GlobalTheory.PsCo.Plug.ellTrace_of_middleX MainStatements.WeightKernel.regClassInt_holds (GlobalTheory.T.siegel_implies_regular_class_finite CompanionTheory.Prw.siegelCore_holds) (GlobalTheory.T.cuspidalOperators_vanishingRadicalIntegrals_unitaryGroup tc)
    GlobalTheory.PsCo.Plug.parabolicT GlobalTheory.IwahoriEigenObj.iwahoriEigenvalues GlobalTheory.T.regularSemisimple_unitaryGroup_concrete GlobalTheory.PsCo.Plug.nonFieldT
    (GlobalTheory.PsCo.Plug.hyperZero_of_intX MainStatements.WeightKernel.regClassInt_holds GlobalTheory.T.regularSemisimple_unitaryGroup_concrete)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section General

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  [Algebra c.F C] [StarRing (𝓞 E)]

theorem fg_htLat (P : Point p v O (𝓞 E)) (τ : E →+* ℂ) : (htLat c P τ).FG := by
  classical
  unfold htLat
  split_ifs
  · exact P.fg_latTQuot _ _
  · exact fg_inf P.integers P.fg_latT _

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem exists_isHTFrame (hs : ∀ a : 𝓞 E, star a = H.bar a) (hv : v.Integers O) {T : CDVR} {io : c.F →+* T.Fr}
    (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O)
    (hk : ∀ a, algebraMap O C (kO a) = k (algebraMap T.V T.Fr a)) :
    ∃ y : FrPt Xo c C, IsHTFrame p v O y₀ k y := by
  classical
  letI := io.toAlgebra
  obtain ⟨P, ψ, hP⟩ := GlobalTheory.CompHt.exists_pointOver E H Dw l Xo c p C v O hs hv T io y₀ hy k.toRingHom kO hk
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.allSixLaws.1.secBaseChange E H Dw l Xo c _ C k y₀.1
  obtain ⟨x, hx⟩ := GlobalTheory.CompHt.TieFrame.exists_lieTie_of_frMap E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz
  have hli : ∀ τ, LinearIndependent C fun j => P.bLie (x τ j) := fun τ =>
    (GlobalTheory.CompHt.alC_surjective_and_linearIndependent_bLie p C v O (𝓞 E) P (GlobalTheory.T.hodgeTate_inclusion_raynaudExtension_algebraicPoint E H Dw l Xo c p C v O T io y₀ hy k.toRingHom kO P ψ hP)).2 _ (x τ)
      (GlobalTheory.CompHt.linearIndependent_evLie_of_lieTie E H Dw l Xo c p C v O T io y₀ k kO P ψ z hP hz τ (x τ) (hx τ))
  have hmem : ∀ τ j, P.bLie (x τ j) ∈ htLat c P τ := fun τ j =>
    wRec_le_htLat P τ ⟨⟨x τ j, (hx τ j).isEig hP (z.eig τ j)⟩, rfl⟩
  choose g hg0 hg1 hg2 using fun τ => GlobalTheory.CompHt.FlagBasis.exists_adapted_basis O C P.V v hv (Dw.mult τ) (htLat c P τ) (fg_htLat P τ)
    (fun j => P.bLie (x τ j)) (hli τ) fun j => ⟨1, one_ne_zero, by rw [one_smul]; exact hmem τ j⟩
  obtain ⟨y, hy', -⟩ := existsUnique_frChg E H Dw l Xo c C z g 1 fun τ => by
    rw [Matrix.det_of_lowerTriangular _ fun i j hij => hg0 τ i j hij]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hg1 τ i).isUnit
  exact ⟨y, (GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c).1.2.2.2.2.1 C y, kO, P, ψ, z, hP, hz, g, _, x, hy', hg0,
    by simp, hx, hg2⟩

end General

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

theorem exists_isHTFrameCp {T : CDVR} {io : c.F →+* T.Fr} (y₀ : IntFr Xo c T io) (hy : y₀.IsAlg) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra c.F ℂ_[p]) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p])
      (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y := by
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hy
  letI := io.toAlgebra
  letI : Algebra c.F ℂ_[p] := (k.comp io).toAlgebra
  letI := H.starRing
  obtain ⟨y, h⟩ := exists_isHTFrame (p := p) (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (O := 𝓞_ℂ_[p]) (fun _ => rfl)
    (PadicComplexInt.integers p) y₀ hy { k with commutes' := fun _ => rfl } kO hk
  exact ⟨p, hp, _, _, y, h⟩

theorem exists_isHTFrameCp_and_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∃ (p : ℕ) (_ : Fact p.Prime) (_ : Algebra c.F ℂ_[p]) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y) ∧ (1 ≤ Dw.p + Dw.q → (∀ q : ℕ, q.Prime → l.GoodAt q) → ∀ (B : ℝ) (la : HeightOneSpectrum (𝓞 c.F)), ((htVals Xo c).1 la).Nonempty ∧ ((mixVals Xo c B).1 la).Nonempty) := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨fun T io y₀ hy => exists_isHTFrameCp y₀ hy, fun hpq hg B la => ?_⟩
  obtain ⟨Z⟩ := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp E H Dw l Xo c).2.2.2 hpq
  have hv : (valSet Xo c (algCls Xo c) la).Nonempty :=
    (GlobalTheory.FlatLine.valOn_nonempty (((GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c).2 hpq).2.2 hg).1 Z la).mono
      (GlobalTheory.FlatLine.valOn_subset Z la)
  have hh : ((htVals Xo c).1 la).Nonempty := by
    obtain ⟨_, ⟨_, T, io, e, ho, y₀, hy, -⟩, -⟩ := hv
    obtain ⟨p, hp, inst, k, y, h⟩ := exists_isHTFrameCp y₀ hy
    exact ⟨_, p, hp, inst, T, io, e, y₀, k, y, ho, hy, h, rfl⟩
  refine ⟨hh, ?_⟩
  simp only [mixVals, ValFam.patch]
  split_ifs
  exacts [hh, hv]

end GlobalTheory.CompHt
end
end

