import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal

namespace GlobalTheory.ToricDenom

def IsClassTerm {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (y : (Af E)ˣ) (T : ℂ) : Prop :=
  ∃ S : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y) S ∧ T = ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0

theorem IsClassTerm.unique {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {c : Ideal (OF E)} {χ : HChar E} {y : (Af E)ˣ} {T T' : ℂ} (h : IsClassTerm φ s κ c χ y T) (h' : IsClassTerm φ s κ c χ y T') :
    T = T' := by
  obtain ⟨S, hS, rfl⟩ := h
  obtain ⟨S', hS', rfl⟩ := h'
  rw [hS.unique hS']

theorem isToricSum_iff {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (T : ℂ) :
    IsToricSum φ s κ c χ T ↔ Finite (PicO c) ∧ ∃ t : PicO c → ℂ, (∀ q, IsClassTerm φ s κ c χ q.out (t q)) ∧ T = ∑ᶠ q, t q := by
  refine and_congr_right fun _ => ⟨fun ⟨S, hS, hT⟩ => ⟨_, fun q => ⟨S q, hS q, rfl⟩, hT⟩, fun ⟨t, ht, hT⟩ => ?_⟩
  choose S hS hS' using ht
  exact ⟨S, hS, by rw [hT]; exact finsum_congr hS'⟩

def IsHostDatum {R : Ranks} (H : Host R) {I : Type} [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E))
    (χ : HChar H.E) : Prop :=
  IsCMType φ ∧ (∀ τ τ', φ τ H.sqrtMinusD = φ τ' H.sqrtMinusD) ∧ 1 ≤ s ∧ (∀ τ, 1 ≤ κ τ) ∧ IsBaseCond 𝔣 ∧ IsValChar φ s κ 𝔣 ∅ χ

def below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (OF E) :=
  P.under (OF E)

theorem over_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Over P (below P) := rfl

open Classical in

def belowSet {E : Type} [Field E] [NumberField E] (Q : Finset (HeightOneSpectrum (𝓞 E))) : Finset (HeightOneSpectrum (OF E)) :=
  Q.image below

theorem splits_below {R : Ranks} (H : Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : Splits (below P) := by
  obtain ⟨x, hx, hx'⟩ := h
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  have hc : ∀ a : 𝓞 H.E, ((c a : 𝓞 H.E) : H.E) = H.conj (a : H.E) := fun a => rfl
  refine ⟨P, P.comap c.toRingHom c.surjective, fun e => ?_, rfl, ?_⟩
  · have : x ∈ (P.comap c.toRingHom c.surjective).asIdeal := e ▸ hx
    exact hx' (c x) (hc x) this
  · ext a
    have : c (algebraMap (OF H.E) (𝓞 H.E) a) = algebraMap (OF H.E) (𝓞 H.E) a := by
      apply RingOfIntegers.ext
      apply H.φ₀.injective
      show H.φ₀ (H.conj ((a : maximalRealSubfield H.E) : H.E)) = H.φ₀ ((a : maximalRealSubfield H.E) : H.E)
      rw [H.toHostAx.conjE_apply]
      exact (a : maximalRealSubfield H.E).2 H.φ₀
    show c (algebraMap (OF H.E) (𝓞 H.E) a) ∈ P.asIdeal ↔ algebraMap (OF H.E) (𝓞 H.E) a ∈ P.asIdeal
    rw [this]

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

abbrev Kbar (i : X.Tw) : Type := AlgebraicClosure (FractionRing (X.O i))

def toBar (i : X.Tw) : FractionRing (X.O0 i) →+* Kbar X i :=
  (algebraMap (FractionRing (X.O i)) (Kbar X i)).comp
    (IsFractionRing.lift (g := (algebraMap (X.O i) (FractionRing (X.O i))).comp (algebraMap (X.O0 i) (X.O i)))
      ((IsFractionRing.injective (X.O i) (FractionRing (X.O i))).comp (X.O_inj i)))

def IsRecMap (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) {c : Ideal (OF D.host.E)} (π : PicO c →* X.RCG i Q) : Prop :=
  ∀ P, P ∉ X.S0 i → P ∉ Q → ∀ σ : G D.host.E N.Om, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ →
    π (QuotientGroup.mk (unifAt P)) = (X.art i Q σ)⁻¹

def IsToricEltAt (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (s : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E)
    (u : Kbar X i),
    IsHostDatum D.host φ s κ 𝔣 χ ∧
    (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
    (∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (val χ P : ℂ) = 1) ∧
    u ≠ 0 ∧
    ∀ Q, BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q)

def atSide {i : X.Tw} (b : Bool) (ι : ℂ →+* Kbar X i) : ℂ →+* Kbar X i := if b then ι else ι.comp (starRingEnd ℂ)

def IsToricElt : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s → IsToricEltAt X i (atSide X (X.sideL i lam) ι) lam s

variable {X}

theorem placesBelow_splitCoprimeConductor_of_admissible {i : X.Tw} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))} (hQ : BlochKatoReduction.Gen.QOk X i Q) {𝔣 : Ideal (OF D.host.E)}
    (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) :
    IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q) ∧ ∀ q ∈ belowSet Q, ((X.l i : ℕ) : OF D.host.E) ∉ q.asIdeal := by
  classical
  constructor
  · intro q hq
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨splits_below D.host (hQ.1 P hP), fun h => Finset.disjoint_left.1 hQ.2.1 hP (h𝔣 P h)⟩
  · intro q hq h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine Finset.disjoint_left.1 hQ.2.1 hP (X.twistExcludedPlaces_contains_residueChar i ?_)
    have : algebraMap (OF D.host.E) (𝓞 D.host.E) ((X.l i : ℕ) : OF D.host.E) ∈ P.asIdeal := h
    rwa [map_natCast] at this

end Record

end GlobalTheory.ToricDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RestrictionH1MemBlochKato
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BKIntegralToRational

theorem exists_mul_pow_eq {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {p : A}
    (hu : ¬ IsUnit p) (a : FractionRing A) :
    ∃ (x : A) (N : ℕ), a * algebraMap A (FractionRing A) p ^ N = algebraMap A (FractionRing A) x := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd0 hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hu
  obtain ⟨c, hc⟩ : d ∣ p ^ N := hN.dvd.trans (pow_dvd_pow_of_dvd h1 N)
  refine ⟨n * c, N, ?_⟩
  have hd1 : algebraMap A (FractionRing A) d ≠ 0 := by
    simpa using hd0
  rw [← map_pow, hc, map_mul, map_mul]
  field_simp

theorem continuous_div_mk {O₀ O' : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [TopologicalSpace O₀] [IsTopologicalRing O₀] (had : IsAdic (IsLocalRing.maximalIdeal O₀))
    [CommRing O'] [IsDomain O'] (ι : O₀ →+* O') {d : O₀} (hd : d ≠ 0) (hd' : ι d ≠ 0) :
    Continuous fun x : O₀ => (Submodule.Quotient.mk (algebraMap O' (FractionRing O') (ι x) /
      algebraMap O' (FractionRing O') (ι d)) : KmodO O') := by
  have hd1 : algebraMap O' (FractionRing O') (ι d) ≠ 0 := by simpa using hd'
  have hop : IsOpen ((Ideal.span {d} : Ideal O₀) : Set O₀) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
    obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
    have := (isAdic_iff.1 had).1 N
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at this
    rwa [Ideal.span_singleton_eq_span_singleton.2 hN]
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((Ideal.span {d} : Ideal O₀) : Set O₀),
    hop.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ : d ∣ y - x := Ideal.mem_span_singleton.1 hy
  rw [Submodule.Quotient.eq]
  refine ⟨ι c, ?_⟩
  rw [← sub_div, ← map_sub, ← map_sub, hc, map_mul, map_mul]
  simp only [Algebra.linearMap_apply]
  field_simp

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem continuous_of_toLL {X : Type} [TopologicalSpace X] (f : X → O₀)
    (h : Continuous fun x => Bw.toLL (f x)) : Continuous f := by
  have h1 : Continuous fun x => Bw.eO (f x) := continuous_induced_rng.2 h
  simpa [Function.comp_def] using Bw.eO_symm_cont.comp h1

theorem continuous_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (j : Fin m) : Continuous fun g => f g j := by
  apply continuous_of_toLL Bw
  have := ((continuous_apply j).comp hf.1.1).comp Bw.e_cont
  simpa [Function.comp_def] using this

theorem cocycle_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (g h : ↥Gw) (j : Fin m) :
    f (g * h) j = f g j + ∑ b, ((T g : GL (Fin m) O₀) : Matrix (Fin m) (Fin m) O₀) j b * f h b := by
  apply toLL_injective Bw
  have := congrFun (hf.1.2 (Bw.e g) (Bw.e h)) j
  simpa [← map_mul, LocBridge.rep, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply] using this

end Bridge

section Main

variable (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ)

theorem l_ne_zero : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := by
  have : CharZero (FractionRing (D.ntw.O0 i)) :=
    (D.ntw.emb0 i).charZero_iff (D.ntw.emb0 i).injective |>.1 inferInstance
  have : CharZero (D.ntw.O0 i) := (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero
  exact Nat.cast_ne_zero.2 (Fact.out : (D.ntw.l i).Prime).ne_zero

theorem toOk_injective : Function.Injective (toOk D i k) :=
  (D.ntw.Ok_inj i k).comp (D.ntw.O_inj i)

theorem l_not_unit : ¬ IsUnit ((D.ntw.l i : ℕ) : D.ntw.Ok i k) := by
  have := D.ntw.Ok_fin i k
  have : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i k)
  intro h
  have h2 : IsUnit (algebraMap (D.ntw.O i) (D.ntw.Ok i k) (D.ntw.l i)) := by simpa using h
  exact D.ntw.O_l i ((isUnit_map_iff _ _).1 h2)

theorem latT_eq : latT D i s = Gen.Tgl i s := rfl

theorem trep_apply (ψ : GE D →* (D.ntw.Ok i k)ˣ) (g : GE D) (hg : ψ g = 1)
    (x : Fin D.R.r → KmodO (D.ntw.Ok i k)) (a : Fin D.R.r) :
    Gen.Trep i s k ψ g x a = ∑ b, toOk D i k
      (((latT D i s g : GL (Fin D.R.r) (D.ntw.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) _) a b) • x b := by
  have h : toOk D i k = Gen.phiK D.ntw i k := rfl
  simp [latT_eq, h, hg, Gen.Trep, twRep, matAct, Gen.Tgl_coe, Gen.Tmat, Finset.smul_sum, smul_smul]

variable (ψ : GE D →* (D.ntw.Ok i k)ˣ) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i))
  (hψ : ∀ σ ∈ decAt D v, ψ σ = 1)

theorem mk_mem_bk (bkP : BK D)
    (z : ReciprocityTheory.Gal.Z1 ((Gen.Trep i s k ψ).comp (Gen.DecV D.nd v).subtype))
    (c : ↥(Loc.GK (bkP.br i v hv).Kw) → Fin D.R.r → ↥(bkP.br i v hv).LL.1)
    (y : ↥(decAt D v) → Fin D.R.r → FractionRing (D.ntw.Ok i k))
    (hc : c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (Gen.PDv bkP i v hv) (Gen.repV bkP i v hv (Gen.Tgl i s)))
    (hy : ∀ g a, Gen.IsImgK bkP i v hv k (c ((bkP.br i v hv).e g) a) (y g a))
    (hz : ∀ g a, (z : ↥(decAt D v) → Fin D.R.r → KmodO (D.ntw.Ok i k)) g a =
      Submodule.Quotient.mk (y g a)) :
    (Submodule.Quotient.mk z : ReciprocityTheory.Gal.H1 _) ∈ Gen.bk bkP i s k ψ v := by
  unfold Gen.bk
  split
  · exact Submodule.subset_span ⟨z, c, y, hc, hy, hz, rfl⟩
  · contradiction

include hψ in

theorem div_mem {f : ↥(decAt D v) → Fin D.R.r → D.ntw.O0 i}
    (hf : IsCrysCocycle (D.ntwbr i v hv) (D.loc (D.ntw.l i)) (latT D i s) f) {d : D.ntw.O0 i}
    (hd : d ≠ 0) :
    ∃ z : ReciprocityTheory.Gal.Z1 ((Gen.Trep i s k ψ).comp (decAt D v).subtype),
      (∀ g j, (z : ↥(decAt D v) → Fin D.R.r → KmodO (D.ntw.Ok i k)) g j = Submodule.Quotient.mk
        (algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k (f g j)) /
          algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k d))) ∧
      (Submodule.Quotient.mk z : ReciprocityTheory.Gal.H1 _) ∈ Gen.bk (bk0 D) i s k ψ v := by
  have hd' : toOk D i k d ≠ 0 := (map_ne_zero_iff _ (toOk_injective D i k)).2 hd
  have hd1 : algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k d) ≠ 0 := by simpa using hd'
  have hd2 : (D.ntwbr i v hv).toLL d ≠ 0 := (map_ne_zero_iff _ (toLL_injective _)).2 hd
  refine ⟨⟨fun g j => Submodule.Quotient.mk
        (algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k (f g j)) /
          algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k d)), ?_, fun g h => ?_⟩,
    fun _ _ => rfl, ?_⟩
  · exact continuous_pi fun j => (continuous_div_mk (D.ntw.twistBaseCoefficientRing_isAdic i) (toOk D i k) hd hd').comp
      (continuous_of_crys _ _ hf j)
  · funext j
    rw [Pi.add_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, trep_apply D i s k ψ g (hψ g g.2)]
    beta_reduce
    rw [cocycle_of_crys _ _ hf g h j]
    simp only [← Submodule.mkQ_apply, map_add, map_sum, map_mul, add_div, Finset.sum_div, mul_div_assoc,
      ← LinearMap.map_smul, Algebra.smul_def]
  · refine mk_mem_bk D i s k ψ v hv (bk0 D) _ (((D.ntwbr i v hv).toLL d)⁻¹ •
      (fun g j => (D.ntwbr i v hv).toLL (f ((D.ntwbr i v hv).e.symm g) j)))
      (fun g j => algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k (f g j)) /
          algebraMap _ (FractionRing (D.ntw.Ok i k)) (toOk D i k d))
      (Submodule.smul_mem _ _ hf) (fun g a => ⟨f g a, d, ⟨hd, ?_⟩, ?_⟩) (fun _ _ => rfl)
    · change (D.ntwbr i v hv).toLL d * (((D.ntwbr i v hv).toLL d)⁻¹ *
        (D.ntwbr i v hv).toLL (f ((D.ntwbr i v hv).e.symm ((D.ntwbr i v hv).e g)) a)) =
          (D.ntwbr i v hv).toLL (f g a)
      rw [MulEquiv.symm_apply_apply, mul_inv_cancel_left₀ hd2]
    · exact mul_div_cancel₀ _ hd1

end Main

end GlobalTheory.BKIntegralToRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelMem

open Polynomial in

theorem mem_range_of_isIntegral {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {α : ℂ}
    (hα : IsIntegral ℚ α) : α ∈ Set.range ε := by
  have h0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hα
  have e : ((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
  have hb : α ∈ (((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε).roots := by
    rw [e, Polynomial.mem_roots (Polynomial.map_ne_zero h0), Polynomial.IsRoot,
      ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ α
  rw [Polynomial.Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

theorem isIntegral_ee {M : ℕ} (hM : 0 < M) : IsIntegral ℚ (ee (1 / (M : ℂ))) := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h : ee (1 / (M : ℂ)) ^ M = 1 := by
    rw [ee, ← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * Real.pi * Complex.I * (1 / M)) = 2 * Real.pi * Complex.I := by field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  exact IsIntegral.of_pow hM (by rw [h]; exact isIntegral_one)

theorem isIntegral_of_mem_adjoin {M : ℕ} (hM : 0 < M) {z : ℂ}
    (hz : z ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) : IsIntegral ℚ z := by
  haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_ee hM)
  have h := Algebra.IsIntegral.isIntegral (R := ℚ) (⟨z, hz⟩ : IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))})
  exact IntermediateField.isIntegral_iff.1 h

theorem act_zero (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 0 = x 0 * (γ 0 0 : ℚ) + x 1 * (γ 1 0 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem act_one' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 1 = x 0 * (γ 0 1 : ℚ) + x 1 * (γ 1 1 : ℚ) := by
  simp [act, Fin.sum_univ_two]

theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : admitted c x) (γ : SL(2, ℤ)) : admitted c (act x γ) := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hx.2.2 ⟨⟨m0 * γ 1 1 - m1 * γ 1 0, ?_⟩, ⟨m1 * γ 0 0 - m0 * γ 0 1, ?_⟩⟩⟩
  all_goals
    have hdet : ((γ 0 0 : ℤ) : ℚ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at this
      exact_mod_cast this
    rw [act_zero] at hm0
    rw [act_one'] at hm1
    push_cast
  · linear_combination (γ 1 1 : ℚ) * hm0 - (γ 1 0 : ℚ) * hm1 + ((c : ℚ) * x 0) * hdet
  · linear_combination (γ 0 0 : ℚ) * hm1 - (γ 0 1 : ℚ) * hm0 + ((c : ℚ) * x 1) * hdet

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem exp_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {c M : ℕ} (hM : 0 < M)
    {y : Fin 2 → ℚ} (P : Fin 2 → ℤ) (hP : ∀ i, (M : ℚ) * y i = P i) (hy : admitted c y) :
    ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c y τ) := by
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : ∀ i, ((P i % (M : ℤ)).toNat : ℚ) = ((P i % (M : ℤ) : ℤ) : ℚ) := fun i => by
    rw [← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)]
  have hlt : (P 0 % (M : ℤ)).toNat < M := by
    have := Int.emod_lt_of_pos (P 0) (by exact_mod_cast hM : (0 : ℤ) < M)
    omega
  set a0 : ℕ := (P 0 % (M : ℤ)).toNat with ha0
  set a1 : ℕ := (P 1 % (M : ℤ)).toNat with ha1
  set x' : Fin 2 → ℚ := ![(a0 : ℚ) / M, (a1 : ℚ) / M] with hx'
  have hx'i : ∀ i, x' i = ((P i % (M : ℤ) : ℤ) : ℚ) / M := fun i => by
    fin_cases i
    · simp [x', ha0, hr]
    · simp [x', ha1, hr]
  set n : Fin 2 → ℤ := fun i => P i / (M : ℤ) with hn
  have hyx : y = fun i => x' i + n i := by
    funext i
    have h1 : y i = (P i : ℚ) / M := by rw [← hP i]; field_simp
    have h2 : (P i : ℚ) = (M : ℚ) * ((P i / (M : ℤ) : ℤ) : ℚ) + ((P i % (M : ℤ) : ℤ) : ℚ) := by
      have h3 : P i = (M : ℤ) * (P i / (M : ℤ)) + P i % (M : ℤ) := by rw [Int.emod_def]; ring
      exact_mod_cast h3
    rw [h1, hx'i, h2]
    simp only [n]
    field_simp
    ring
  have hadm : admitted c x' := by
    refine ⟨hy.1, hy.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hy.2.2 ⟨⟨m0 + c * n 0, ?_⟩, ⟨m1 + c * n 1, ?_⟩⟩⟩
    · rw [hyx]; push_cast; rw [hm0]; ring
    · rw [hyx]; push_cast; rw [hm1]; ring
  have hper : ∀ τ : ℍ, sg c y τ = sg c x' τ := fun τ => by
    rw [hyx]; exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x' n τ hadm
  obtain ⟨k, hk⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a0 hM hlt
  obtain ⟨A, hQ, -, hA, -, -⟩ := hk a1 hadm
  have hε : ∀ j, ε (Function.invFun ε (A j)) = A j := fun j =>
    Function.invFun_eq (mem_range_of_isIntegral ε (isIntegral_of_mem_adjoin hM (hA j)))
  classical
  refine ⟨fun m => if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0, k,
    fun m hm => by simp [not_le.2 hm], fun τ => ?_⟩
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + k) := fun i j h => by simpa using h
  rw [← Function.Injective.hasSum_iff hinj (fun m hm => by
    have : ¬ k ≤ m := fun h => hm ⟨(m - k).toNat, by simp; omega⟩
    simp [this])]
  have h1 := (hQ τ).mul_left (ee ((k : ℂ) / M * (τ : ℂ)))
  have key : ee ((k : ℂ) / M * (τ : ℂ)) * (sg c x' τ * ee (-((k : ℂ) / M) * (τ : ℂ))) = sg c y τ := by
    rw [hper, mul_left_comm, ee, ee, ← Complex.exp_add]
    have : 2 * ↑Real.pi * Complex.I * ((k : ℂ) / ↑M * ↑τ) + 2 * ↑Real.pi * Complex.I * (-((k : ℂ) / ↑M) * ↑τ) = 0 := by
      ring
    rw [this, Complex.exp_zero, mul_one]
  rw [key] at h1
  have e : (fun m : ℤ => ε (if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / M)) ∘ (fun j : ℕ => (j : ℤ) + k) =
      fun j : ℕ => ee ((k : ℂ) / M * (τ : ℂ)) * (A j * Complex.exp (2 * Real.pi * Complex.I * j * τ / M)) := by
    funext j
    simp only [Function.comp_apply, le_add_iff_nonneg_left, Nat.cast_nonneg, if_true, add_sub_cancel_right,
      Int.toNat_natCast, hε]
    rw [mul_left_comm, ee, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact e ▸ h1

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

theorem an_siegel_eq : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), admitted c x → T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  intro Ω _ _ _ ε T c x hx
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  set M : ℕ := (x 0).den * (x 1).den with hMdef
  have hM : 0 < M := Nat.mul_pos (x 0).den_pos (x 1).den_pos
  set Px : Fin 2 → ℤ := ![(x 0).num * (x 1).den, (x 1).num * (x 0).den] with hPx
  have hMx : ∀ i, (M : ℚ) * x i = Px i := fun i => by
    fin_cases i
    · simp only [hMdef, hPx, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 0)]; ring
    · simp only [hMdef, hPx, Matrix.cons_val_one, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 1)]; ring
  have hd : DifferentiableOn ℂ (sgC c x) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c x hx)
  have hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ := by
    intro γ hγ τ
    haveI : NeZero M := ⟨hM.ne'⟩
    obtain ⟨g00, g01, g10, g11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have d00 : (M : ℤ) ∣ γ 0 0 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g00, sub_self])
    have d01 : (M : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g01
    have d10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g10
    have d11 : (M : ℤ) ∣ γ 1 1 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g11, sub_self])
    obtain ⟨t00, h00⟩ := d00
    obtain ⟨t01, h01⟩ := d01
    obtain ⟨t10, h10⟩ := d10
    obtain ⟨t11, h11⟩ := d11
    have e : act x γ = fun i => x i + (![Px 0 * t00 + Px 1 * t10, Px 0 * t01 + Px 1 * t11] : Fin 2 → ℤ) i := by
      have q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * t00 := by
        have : γ 0 0 = 1 + M * t00 := by rw [← h00]; ring
        rw [this]; push_cast; ring
      have q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * t11 := by
        have : γ 1 1 = 1 + M * t11 := by rw [← h11]; ring
        rw [this]; push_cast; ring
      have q01 : ((γ 0 1 : ℤ) : ℚ) = M * t01 := by rw [h01]; push_cast; ring
      have q10 : ((γ 1 0 : ℤ) : ℚ) = M * t10 := by rw [h10]; push_cast; ring
      have r0 : act x γ 0 = x 0 + ((Px 0 * t00 + Px 1 * t10 : ℤ) : ℚ) := by
        rw [act_zero, q00, q10]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      have r1 : act x γ 1 = x 1 + ((Px 0 * t01 + Px 1 * t11 : ℤ) : ℚ) := by
        rw [act_one', q01, q11]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      funext i
      fin_cases i
      · simpa using r0
      · simpa using r1
    rw [e]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x _ τ hx
  refine SiegelModel.an_siegel T M hM hd (fun γ τ => GlobalTheory.T.siegel_function_transformation c x γ τ hx) hlev (fun γ => ?_)
  refine exp_int ε hM (fun i => Px 0 * γ 0 i + Px 1 * γ 1 i) (fun i => ?_) (admissible_act_SL2 hx γ)
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [← hMx 0, ← hMx 1]
  ring

end GlobalTheory.KZ.SiegelMem
end
end

