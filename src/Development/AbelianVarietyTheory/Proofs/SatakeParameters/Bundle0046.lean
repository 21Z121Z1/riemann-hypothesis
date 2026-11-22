import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0042
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingMapsIntoGoodExtension
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem good_conjugates_mem : ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (s : ℕ),
    Loc.Good K s LL → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1 := by
  intro l _ K LL s h τ x
  unfold Loc.Good at h
  obtain ⟨-, -, hle, hall⟩ := h

  let σ := τ.liftNormal (Loc.Om l)
  have hσ : σ (algebraMap K.1 (Loc.Om l) x) = τ x := by
    rw [AlgHom.liftNormal_commutes]
    rfl
  have hx := hall ((σ : Loc.Om l →ₐ[ℚ_[l]] Loc.Om l).comp (Loc.Ks K s).val) ⟨x, hle x.2⟩
  rw [← hσ]
  exact hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNeg
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem signs_alternate_inert : ∀ {fr : Formalism.HC.Frame} (ε : ℤˣ) (τ φ : fr.GG), φ.1.2 = -1 →
    Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) ∧
      Alternates (fun i : ZMod (orderOf φ) => !pos ε (letter τ φ i)) := by
  intro e ε τ φ hφ
  have hsnd : ∀ k : ℕ, (τ * φ ^ k).1.2 = τ.1.2 * (-1) ^ k := by
    intro k; simp [Prod.snd_mul, Prod.fst_mul, Prod.pow_fst, Prod.pow_snd, hφ]
  have hn : 0 < orderOf φ := orderOf_pos φ
  have h1 : ((-1 : ℤˣ)) ^ orderOf φ = 1 := by
    have h : (φ ^ orderOf φ).1.2 = 1 := by rw [pow_orderOf_eq_one]; rfl
    rwa [Prod.pow_fst, Prod.pow_snd, hφ] at h
  haveI : NeZero (orderOf φ) := ⟨hn.ne'⟩
  have key : ∀ i : ZMod (orderOf φ), (letter τ φ (i + 1)).1.2 = -(letter τ φ i).1.2 := by
    intro i
    unfold letter
    rw [hsnd, hsnd, ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    have hm : ((-1 : ℤˣ)) ^ ((i.val + 1) % orderOf φ) = (-1) ^ (i.val + 1) := by
      conv_rhs => rw [← Nat.mod_add_div (i.val + 1) (orderOf φ), pow_add, pow_mul, h1, one_pow, mul_one]
    rw [hm, pow_succ]
    simp
  have hA : Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) := by
    intro i
    simp only [pos]
    rw [key i]
    rcases Int.units_eq_one_or (letter τ φ i).1.2 with h | h <;>
      rcases Int.units_eq_one_or ε with h' | h' <;> simp [h, h'] <;> decide
  refine ⟨hA, fun i => ?_⟩
  have h := hA i
  simp only at h ⊢
  rw [h]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedByRepMatricesOfScalarExtension
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem endSpanned_of_endSpanned_map {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ}
    (τ : Γ →* GL (Fin a) L) (U : Submodule L (Fin a → L))
    (h : EndSpanned (mapRep f τ) (Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L))))) :
    EndSpanned τ U := by
  classical
  intro φ
  set UE := Submodule.span E ((fun v => f ∘ v) '' (U : Set (Fin a → L))) with hUE
  have hmap : ∀ (M : Matrix (Fin a) (Fin a) L) (v : Fin a → L),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v
    funext i
    exact (RingHom.map_mulVec f M v i).symm

  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype U)
  set Y : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' (U.subtype ∘ₗ φ ∘ₗ p) with hY
  have hYv : ∀ v : Fin a → L, Y.mulVec v = (φ (p v) : Fin a → L) := by
    intro v
    rw [hY, LinearMap.toMatrix'_mulVec]
    rfl
  have hYU : ∀ w : U, Y.mulVec (w : Fin a → L) = (φ w : Fin a → L) := by
    intro w
    rw [hYv]
    have : p (w : Fin a → L) = w := by
      have := LinearMap.congr_fun hp w
      simpa using this
    rw [this]
  have hYE : ∀ x ∈ UE, (Y.map f).mulVec x ∈ UE := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [hmap, hYv]
      exact Submodule.subset_span ⟨_, (φ (p v)).2, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact UE.add_mem hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact UE.smul_mem c hx
  let ψ : UE →ₗ[E] UE := (Matrix.mulVecLin (Y.map f)).restrict hYE
  obtain ⟨XE, hXE, hXEw⟩ := h ψ

  let d := Module.finrank L U
  let b := Module.finBasis L U
  let Φ : Matrix (Fin a) (Fin a) L →ₗ[L] (Fin a × Fin d → L) :=
    { toFun := fun M ik => (M.mulVec (b ik.2 : Fin a → L)) ik.1
      map_add' := by intro M N; funext ik; simp [Matrix.add_mulVec]
      map_smul' := by intro c M; funext ik; simp [Matrix.smul_mulVec] }
  let ΦE : Matrix (Fin a) (Fin a) E →ₗ[E] (Fin a × Fin d → E) :=
    { toFun := fun M ik => (M.mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1
      map_add' := by intro M N; funext ik; simp [Matrix.add_mulVec]
      map_smul' := by intro c M; funext ik; simp [Matrix.smul_mulVec] }
  set R := Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) with hR
  set RE := Set.range fun g => ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) with hRE
  have hrep : ∀ g, ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)
      = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).map f := fun g => rfl
  have hΦE : ∀ M : Matrix (Fin a) (Fin a) L, ΦE (M.map f) = f ∘ Φ M := by
    intro M
    funext ik
    show ((M.map f).mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = f ((M.mulVec (b ik.2 : Fin a → L)) ik.1)
    rw [hmap]; rfl
  set t : Fin a × Fin d → L := fun ik => (φ (b ik.2) : Fin a → L) ik.1 with ht
  have hXt : ΦE XE = f ∘ t := by
    funext ik
    have hmem : f ∘ (b ik.2 : Fin a → L) ∈ UE := Submodule.subset_span ⟨_, (b ik.2).2, rfl⟩
    have := hXEw ⟨_, hmem⟩
    show (XE.mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = f ((φ (b ik.2) : Fin a → L) ik.1)
    rw [this]
    show ((Y.map f).mulVec (f ∘ (b ik.2 : Fin a → L))) ik.1 = _
    rw [hmap, hYU]
    rfl
  have hEspan : f ∘ t ∈ Submodule.span E ((fun v => f ∘ v) '' (Φ '' R)) := by
    rw [← hXt]
    have h1 : ΦE XE ∈ Submodule.map ΦE (Submodule.span E RE) := Submodule.mem_map_of_mem hXE
    rw [Submodule.map_span] at h1
    convert h1 using 2
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, hΦE _⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, (hΦE _).symm⟩
  have hLspan := mem_span_of_map_mem_span f (Φ '' R) t hEspan
  rw [← Submodule.map_span] at hLspan
  obtain ⟨X, hX, hXt'⟩ := hLspan
  refine ⟨X, hX, fun w => ?_⟩
  have hb : ∀ k, X.mulVec (b k : Fin a → L) = (φ (b k) : Fin a → L) := by
    intro k
    funext i
    exact congrFun hXt' (i, k)
  have hext : (Matrix.mulVecLin X) ∘ₗ U.subtype = U.subtype ∘ₗ φ := b.ext fun k => by
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Submodule.subtype_apply]
    exact hb k
  exact LinearMap.congr_fun hext w

end GlobalTheory.SplitField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjDoubleBlockOfIsoSubspacesStatement
section
open Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_double_block_of_iso_subspaces : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsSSRep ρ → IsInv ρ W₁ → IsInv ρ W₂ → W₁ ≠ ⊥ → W₁ ⊓ W₂ = ⊥ → IsoSub ρ W₁ W₂ → ∃ (d u : ℕ) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (h : d + d + u = a) (Pm : GL (Fin a) k), 0 < d ∧ ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k) := by
  first | exact @GlobalTheory.DoubleBlock.exists_conj_double | exact GlobalTheory.DoubleBlock.exists_conj_double | (intros; apply GlobalTheory.DoubleBlock.exists_conj_double <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInternalStableDecompositionDescendsToSubfi
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

def coordMap {L E : Type} [Field L] [Field E] (f : L →+* E) (a : ℕ) :
    (Fin a → L) →ₛₗ[f] (Fin a → E) where
  toFun v := f ∘ v
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp [smul_eq_mul]

theorem coordMap_injective {L E : Type} [Field L] [Field E] (f : L →+* E) (a : ℕ) :
    Function.Injective (coordMap f a) := by
  intro v w h
  funext i
  exact f.injective (congrFun h i)

theorem descend_decomp {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ}
    (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)) (hint : DirectSum.IsInternal Vs)
    (hinv : ∀ m, IsInv (mapRep f τ) (Vs m))
    (hspan : ∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) :
    ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧
      ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  classical
  set F := coordMap f a with hF
  let Us : Fin n → Submodule L (Fin a → L) := fun m => (Vs m).comap F
  have hUs : ∀ m, (Us m : Set (Fin a → L)) = {v : Fin a → L | f ∘ v ∈ Vs m} := fun m => rfl
  obtain ⟨hindV, htopV⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Vs).1 hint
  refine ⟨Us, ?_, fun m => ⟨?_, ?_⟩⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      intro v hv1 hv2
      have hle : (⨆ (j : Fin n) (_ : j ≠ i), Us j) ≤ (⨆ (j : Fin n) (_ : j ≠ i), Vs j).comap F :=
        iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => Vs j) j hj)
      have h1 : F v ∈ Vs i := hv1
      have h2 : F v ∈ ⨆ (j : Fin n) (_ : j ≠ i), Vs j := hle hv2
      have h3 := (Submodule.disjoint_def.1 ((iSupIndep_def.1 hindV) i)) _ h1 h2
      exact coordMap_injective f a (by rw [h3, map_zero])
    · rw [eq_top_iff]
      intro v _
      have hle : (⨆ m, Vs m) ≤ Submodule.span E ((fun v => f ∘ v) '' ((⨆ m, Us m : Submodule L (Fin a → L)) : Set (Fin a → L))) := by
        refine iSup_le fun m => (hspan m).trans (Submodule.span_mono (Set.image_mono ?_))
        rw [← hUs m]
        exact le_iSup Us m
      have hv : f ∘ v ∈ ⨆ m, Vs m := by rw [htopV]; exact Submodule.mem_top
      have := mem_span_of_map_mem_span f _ v (hle hv)
      rwa [Submodule.span_eq] at this
  · intro g v hv
    have hv' : f ∘ v ∈ Vs m := hv
    show f ∘ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v ∈ Vs m
    have hm : f ∘ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v =
        ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).mulVec (f ∘ v) := by
      funext i
      exact RingHom.map_mulVec f _ v i
    rw [hm]
    exact hinv m g _ hv'
  · refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact hv
    · rw [hUs m]
      exact hspan m

end GlobalTheory.SplitField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
section
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem exists_aut_comp_eq_of_normal {E L : Type} [Field E] [CharZero E] [Normal ℚ E] [Field L]
    (f f' : E →+* L) : ∃ σ : E ≃ₐ[ℚ] E, ∀ x, f' x = f (σ x) := by
  haveI : CharZero L := (RingHom.charZero_iff f.injective).1 inferInstance
  letI : Algebra E L := f.toAlgebra
  haveI : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun q => by
    change _ = f (algebraMap ℚ E q)
    simp
  obtain ⟨σ, hσ⟩ := (Normal.algHomEquivAut ℚ L E).symm.surjective f'.toRatAlgHom
  refine ⟨σ, fun x => ?_⟩
  have := DFunLike.congr_fun hσ x
  exact this.symm

theorem exists_letter_of_local_embedding : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), ∃ g : D.R.GG, (∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) = Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x)))) ∧ (Br.EmbTypeU D.nbr i w hw τ ↔ g ∈ D.R.Psi) := by
  intro D i w hw τ
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨σ, hσ⟩ := exists_aut_comp_eq_of_normal
    (((Br.toLLK (D.nbr i w hw)).comp (D.nd.embK i)).comp D.embE)
    ((τ : Br.Kw D.nbr i w hw →+* Br.LL D.nbr i w hw).comp (Br.cEw D.nbr i w hw))
  obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
  have hg' : D.host.sigmaOf g = σ := hg
  have key : ∀ x : D.host.E, τ (Br.cEw D.nbr i w hw x) =
      Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g x))) := by
    intro x
    rw [hg']
    exact hσ x
  have hemb : ∀ x, D.what₂.embLL (D.embE (D.host.sigmaOf g x)) = D.host.emb g x := fun x =>
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)
  refine ⟨g, key, ?_, ?_⟩
  · rintro ⟨-, φ, hφ, h⟩
    have : D.host.emb g = φ := RingHom.ext fun x => by
      rw [← hemb x]
      exact h x _ (key x).symm
    exact ((factEmb D.R D.host).2 g).1 (this ▸ hφ)
  · intro hgP
    refine ⟨fun x => ⟨_, (key x).symm⟩, D.host.emb g, ((factEmb D.R D.host).2 g).2 hgP, ?_⟩
    intro x y hy
    have hy' : y = D.embE (D.host.sigmaOf g x) :=
      (D.nd.embK i).injective ((Br.toLLK (D.nbr i w hw)).injective (hy.trans (key x)))
    rw [hy', hemb]

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceOverPrimeOfPadicAlgClEmbedding
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LocPlace

theorem norm_le_one_of_isIntegral' {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_int_le_one (l : ℕ) [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' (map_isIntegral_int c x.isIntegral_coe)

theorem norm_natCast_prime_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

def ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : Ideal (𝓞 E) where
  carrier := {x | ‖c (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have e : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := by simp
    rw [e, map_add]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro a b hb
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    push_cast
    rw [map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le_one l c a)) hb

theorem mem_ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ ballIdeal l E c ↔ ‖c (x : E)‖ < 1 := Iff.rfl

theorem ballIdeal_isPrime (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : (ballIdeal l E c).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : 𝓞 E) ∈ ballIdeal l E c := h ▸ Submodule.mem_top
    rw [mem_ballIdeal] at h1
    simp at h1
  · intro a b hab
    rw [mem_ballIdeal, mem_ballIdeal] at *
    push_cast at hab
    rw [map_mul, norm_mul] at hab
    by_contra hcon
    push_neg at hcon
    have ha := le_antisymm (norm_int_le_one l c a) hcon.1
    have hb := le_antisymm (norm_int_le_one l c b) hcon.2
    rw [ha, hb] at hab
    norm_num at hab

theorem natCast_mem_ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : ((l : ℕ) : 𝓞 E) ∈ ballIdeal l E c := by
  rw [mem_ballIdeal]
  push_cast
  rw [map_natCast]
  exact norm_natCast_prime_lt_one l

theorem ballIdeal_ne_bot (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : ballIdeal l E c ≠ ⊥ := by
  intro h
  have h1 := natCast_mem_ballIdeal l E c
  rw [h, Ideal.mem_bot] at h1
  have h2 : ((l : ℕ) : E) = 0 := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

theorem exists_place_of_emb : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l), ∃ v : HeightOneSpectrum (𝓞 E), v ∈ placesOver E l ∧
      ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 := by
  intro l _ E _ _ c
  refine ⟨⟨ballIdeal l E c, ballIdeal_isPrime l E c, ballIdeal_ne_bot l E c⟩, ?_, fun x => Iff.rfl⟩
  exact natCast_mem_ballIdeal l E c

end GlobalTheory.LocPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsAtThickEmbedding
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.SizeThick

theorem size_thick {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m) (hT : Thick D.host g) :
    L.sc.b ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dif_pos hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  have hmem : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces := by
    rw [hρ, Equiv.apply_symm_apply]; exact hT
  have h := L.win_thick (j.1 + 1) (by omega) j.2 ρ hmem
  rw [hw] at h
  have hc : hcAt D g = D.hc ρ := rfl
  obtain ⟨z, hz⟩ := (D.hc ρ).e_int j
  rw [hc, hz, Int.floor_intCast]
  rw [hz] at h
  push_cast at h ⊢
  exact h

end GlobalTheory.HTW.SizeThick
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FloorSizeBoundsNotThickEmbedding
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem size_not_thick : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (g : D.R.GG) (j : Fin D.R.m), Roomy L C → ¬ Thick D.host g → L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ 8 / 5 * L.sc.b' := by
  intro D L C g j hR hnt
  obtain ⟨-, hw100, hwη, hwb, hbT, -⟩ := hR
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρe : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dif_pos hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  obtain ⟨z, hz⟩ := (D.hc ρ).e_int j
  have hfl : (⌊(hcAt D g).e j⌋ : ℝ) = wj D (j.1 + 1) ρ := by
    rw [hw]
    show (⌊(D.hc ρ).e j⌋ : ℝ) = (((D.hc ρ).e j : ℚ) : ℝ)
    rw [hz, Int.floor_intCast]; push_cast; rfl
  rw [hfl]
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb' : 0 < L.sc.b' := by linarith
  have hq : 0 < L.sc.b' / L.sc.x := div_pos hb' hx
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hnt' : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρe]; exact hnt
  by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
    obtain ⟨a1, a2⟩ := L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm
    have a3 := L.bT_ge ⟨t, ht'⟩
    have a4 := hbT ⟨t, ht'⟩
    constructor <;> linarith
  · obtain ⟨a1, a2⟩ := L.win_thin _ (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hnt'⟩
    constructor <;> linarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPartRecursion
section
namespace GlobalTheory.Proof.GoodComponentRecursion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem goodPartRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.GoodPartRec D.nd D.naut i := by
  intro D hW h1 hlift hpt hbc hsp i
  exact GlobalTheory.Proof.SplitPlaceGoodSignature.goodPart_of_lifts D.nd D.naut i h1
    (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut hW).1 (hlift i) (hpt i)
    (GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange _ _ _ D.nd D.naut i (hbc i) (hsp i))

end GlobalTheory.Proof.GoodComponentRecursion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeightsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_galois_local_weights : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → SumRepresentations.At.G2 D.nd D.naut i r ∧ SumRepresentations.At.G4 D.nd i r := by
  first | exact @GlobalTheory.NRows.crys_unram_of_lgc | exact GlobalTheory.NRows.crys_unram_of_lgc | (intros; apply GlobalTheory.NRows.crys_unram_of_lgc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisOfUnramifiedMatchStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_galois_of_unramified_match : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := by
  first | exact @GlobalTheory.NRows.isHeckeGaloisQ_of_wdOf_baseChange | exact GlobalTheory.NRows.isHeckeGaloisQ_of_wdOf_baseChange | (intros; apply GlobalTheory.NRows.isHeckeGaloisQ_of_wdOf_baseChange <;> assumption)
end

