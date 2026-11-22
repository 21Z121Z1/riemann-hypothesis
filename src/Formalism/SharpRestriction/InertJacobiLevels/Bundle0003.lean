import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0007
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.SharpRestriction.FamCore
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0002

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraZero
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain

theorem rrDef_of_subsingleton (D : D7) [Subsingleton D.div.RR.V] : DV.RRDef D := by
  intro x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ w => ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [smul_zero]; exact Submodule.zero_mem _⟩, fun _ => Submodule.zero_mem _⟩

theorem nprimeDef_of_subsingleton (D : D7) (L : SizeData₂ D) [∀ u, Subsingleton (D.div.Nu u).V] :
    DV.NprimeDef D L := fun _ => Subsingleton.elim _ _

theorem locLe_of_subsingleton {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    [Subsingleton V] (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (A B : Submodule (𝓞 K) V) : DV.LocLe w k A B :=
  fun x _ => ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [Subsingleton.elim ((1 : 𝓞 K) • x) 0]; exact Submodule.zero_mem _⟩

theorem lenLoc_of_subsingleton {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    [Subsingleton V] (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : DV.lenLoc w A B = 0 := by
  let _ : w.asIdeal.IsPrime := w.isPrime
  unfold DV.lenLoc
  rw [Module.length_eq_zero_iff]
  have h1 : Subsingleton (↥B ⧸ A.comap B.subtype) := by
    have : Subsingleton ↥B := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance
  infer_instance

theorem nuDef_of_subsingleton (D : D7) (L : SizeData₂ D) [∀ u, Subsingleton (D.div.Nu u).V]
    (hl : ∀ u w, L.lenMN u w = 0) : DV.NuDef D L := by
  refine ⟨fun u w _ => locLe_of_subsingleton _ _ _ _, fun u w _ _ =>
    ⟨locLe_of_subsingleton _ _ _ _, locLe_of_subsingleton _ _ _ _⟩, fun u w l h => ?_⟩
  rw [lenLoc_of_subsingleton] at h
  have : l = 0 := by exact_mod_cast h.symm
  rw [this, hl]
  simp

theorem lenMN_zero_of_nuDef (D : D7) (L : SizeData₂ D) [∀ u, Subsingleton (D.div.Nu u).V] (h : DV.NuDef D L)
    (hr : ∀ w, D.what₂.places.ramIdx w ≠ 0) (u : D.what₂.Word) (w : D.what₂.places.Pl) : (L.lenMN u w : ℝ) = 0 := by
  have h1 := h.2.2 u w 0 (by rw [lenLoc_of_subsingleton]; rfl)
  have h2 : L.lenMN u w = 0 ∨ D.what₂.places.ramIdx w = 0 := by simpa using h1.symm
  rcases h2 with h3 | h3
  · rw [h3]; simp
  · exact absurd h3 (hr w)

def lieOfSubsingleton (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [Subsingleton V] [Subsingleton W] : V ≃ₗᵢ[ℂ] W :=
  ⟨LinearEquiv.ofSubsingleton V W, fun x => by
    rw [Subsingleton.elim x 0, map_zero, norm_zero, norm_zero]⟩

set_option synthInstance.maxHeartbeats 200000 in

def rowSideZero (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    [Subsingleton EE] : RowSide D EE where
  Amb := fun _ => Z0
  Mult := fun _ _ => Z0
  multZero := fun _ => lieOfSubsingleton _ _
  multTop := fun _ => LinearIsometryEquiv.refl ℂ Z0
  io := fun _ _ => 0
  Mtilde := fun _ => zeroOLat _
  cen := fun _ => (Representation.trivial ℂ _ _).asAlgebraHom.comp (Subalgebra.val _)
  eOp := fun _ => 0
  eOp_idem := fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  eOp_sa := fun _ _ _ => by simp
  eOp_tie := fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  RR := zeroHLat D.what₂.LL
  RR_frames := (zeroHLat_good D.what₂.LL).1
  jEE := 0
  jEE_basis := ⟨by
    have : IsEmpty (zeroHLat D.what₂.LL).ι := inferInstanceAs (IsEmpty (Fin 0))
    exact linearIndependent_empty_type, Subsingleton.elim _ _⟩
  jEE_norm := fun x => (normAt_empty (ι := Fin 0) _ _ _ _).trans (by simp)

theorem rowSideZero_RRDef (D : D7) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] [Subsingleton EE] : (rowSideZero D EE).RRDef := by
  intro x
  have hx : x = 0 := Subsingleton.elim (α := Fin 0 → D.what₂.LL) x 0
  rw [hx]
  exact ⟨fun _ w => ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [smul_zero]; exact Submodule.zero_mem _⟩, fun _ => Submodule.zero_mem _⟩

def trivialSide (D : D7) [Subsingleton D.what₂.EE0] : BaseLevelRowSide D := ⟨rowSideZero D D.what₂.EE0⟩

theorem trivialSide_rrDef_of_subsingleton (D : D7) [Subsingleton D.what₂.EE0] : (trivialSide D).s.RRDef := rowSideZero_RRDef D _

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.RayPrimes
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

def RayPrimes : Prop :=
  ∀ d M N : ℕ, d.Prime → 0 < M → ∃ (x y : ℤ) (T : ℕ), N < T ∧ T.Prime ∧
    (T : ℤ) = (1 + M * x) ^ 2 + d * (M * y) ^ 2

def TNorm {R : Ranks} (H : Host R) (T : ℕ) : Prop :=
  ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (T : H.E) ∧
    (π - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)}

structure Fits (lb : Bool) (D : D7) {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1)) (u0 : (Rt s).A)
    (T Lw β : ℕ) (Tstar Gam : ℝ) : Prop where
  host_eq : (⟨D.R, D.host⟩ : Σ R : Ranks, Host R) = ⟨Rt s, hostOf A u0 T Lw⟩
  word : ∀ u : D.what₂.Word, u = D.u₀
  letter : ∀ u l, D.s.letter u l = lb
  eta : ∀ j w, D.what₂.etaJ j w = 0
  Aj_eq : ∀ j w, D.what₂.Aj j w = 0
  T_eq : ∀ u, (D.mem u).A.T = T
  Tstar_eq : ∀ u, (D.mem u).A.Tstar = Tstar
  Gam_eq : ∀ u, (D.mem u).A.GamP = Gam
  Del_eq : (D.s.Del : ℝ) = 1
  hv : ∀ τ (i : Fin (D.R.k - 1)), (D.hc τ).v i = 24 - 4 * ((i : ℕ) : ℚ)
  hu0 : ∀ τ (h : 0 < D.R.k), (D.hc τ).u ⟨0, h⟩ = 113 / 2
  hu : ∀ u τ (i : Fin D.R.k), 1 ≤ i.1 → i.1 + 1 < D.R.k → (D.hcW u τ).u i = 55 / 2 - 4 * ((i : ℕ) : ℚ)
  hb : ∀ τ (j : Fin D.R.m), (D.hc τ).b j = β + 2 * ((s : ℚ) + 9) * ((j : ℕ) : ℚ)
  he : ∀ τ (j : Fin D.R.m), (D.hc τ).e j = β + ((s : ℚ) + 9) + 2 * ((s : ℚ) + 9) * ((j : ℕ) : ℚ)

def ToyNormPrimeProp : Prop :=
  ∃ lb : Bool, ∀ (s B : ℕ) (A : Arith B (4 * (2 * s + 15) * 9 + 1)) (u0 : (Rt s).A) (T Lw β : ℕ)
    (Tstar Gam : ℝ), T.Prime → T ≠ 31 → T ≠ 61 → TNorm (hostOf A u0 T Lw) T → 1 ≤ β →
    Tstar ≤ T → (T : ℝ) ≤ (1 + 1 / 64) * Tstar → 1 < Gam →
    ∃ D : D7, Fits lb D A u0 T Lw β Tstar Gam

def SizeDataAt : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x1 : ℝ, 1 < x1 ∧ ∀ x, x1 < x → ∃ (s B Lw β : ℕ) (Gam : ℝ), 1 ≤ β ∧ 1 < Gam ∧
    ∀ (lb : Bool) (D : D7) (A : Arith B (4 * (2 * s + 15) * 9 + 1)) (u0 : (Rt s).A) (T : ℕ) (Tstar : ℝ),
      Real.exp (x ^ eps) ≤ T → Fits lb D A u0 T Lw β Tstar Gam →
      ∃ L : SizeData₂ D, L.sc.x = x ∧ L.sc.eps = eps ∧ L.CGam = 1 ∧ L.Cc = 2 ∧ L.Ct = eps ∧ L.LaG = x ^ eps ∧
        L.supp = ∅

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ResCharConj
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain IsLocalRing

variable (D : D7) (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0)

def toLL0 : D.what₂.LL →+* ↥D.LL0 := (RingHom.id D.what₂.LL).codRestrict D.LL0 hLL0

def phiO : 𝓞 ↥D.LL0 →+* 𝓞 D.what₂.LL := RingOfIntegers.mapRingHom (algebraMap ↥D.LL0 D.what₂.LL)

def psiO : 𝓞 D.what₂.LL →+* 𝓞 ↥D.LL0 := RingOfIntegers.mapRingHom (toLL0 D hLL0)

theorem phi_psi (x : 𝓞 D.what₂.LL) : phiO D (psiO D hLL0 x) = x := RingOfIntegers.ext rfl

def plLL0 (P : HeightOneSpectrum (𝓞 D.what₂.LL)) : HeightOneSpectrum (𝓞 ↥D.LL0) where
  asIdeal := P.asIdeal.comap (phiO D)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : psiO D hLL0 x ∈ P.asIdeal.comap (phiO D) := by
      rw [Ideal.mem_comap, phi_psi]; exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← phi_psi D hLL0 x, h1, map_zero]

theorem cover_at (hc : NTw.TwCover D.ntw) (w : D.what₂.places.Pl) : ∃ i, D.ntw.l i = D.what₂.places.resChar w ∧
    ∀ x : 𝓞 ↥D.LL0, x ∈ (plLL0 D hLL0 (D.plEq w)).asIdeal ↔
      ∃ y ∈ maximalIdeal (D.ntw.O0 i),
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0) :=
  hc _ (D.what₂.places.resChar_prime w) (plLL0 D hLL0 (D.plEq w)) (by
    show phiO D _ ∈ (D.plEq w).asIdeal
    rw [map_natCast]
    exact resChar_mem D w)

def gOk (i : D.ntw.Tw) (k : ℕ) : D.ntw.O0 i →+* D.ntw.Ok i k :=
  (algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))

theorem gOk_inj (i : D.ntw.Tw) (k : ℕ) : Function.Injective (gOk D i k) :=
  (D.ntw.Ok_inj i k).comp (D.ntw.O_inj i)

theorem gOkF_inj (i : D.ntw.Tw) (k : ℕ) : Function.Injective
    ((algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k))).comp (gOk D i k)) :=
  (IsFractionRing.injective _ _).comp (gOk_inj D i k)

def iotaOk (i : D.ntw.Tw) (k : ℕ) : FractionRing (D.ntw.O0 i) →+* FractionRing (D.ntw.Ok i k) :=
  IsFractionRing.lift (gOkF_inj D i k)

theorem iotaOk_alg (i : D.ntw.Tw) (k : ℕ) (y : D.ntw.O0 i) :
    iotaOk D i k (algebraMap _ _ y) = algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k)) (gOk D i k y) :=
  IsFractionRing.lift_algebraMap (gOkF_inj D i k) y

theorem l_ne_zero (i : D.ntw.Tw) : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := by
  intro h
  have h1 : D.ntw.emb0 i ((D.ntw.l i : ℕ) : ↥D.LL0) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))), h, map_zero]
  have h2 := (map_eq_zero (D.ntw.emb0 i)).1 h1
  have h3 : (D.ntw.l i : ℕ) = 0 := by exact_mod_cast h2
  exact (Fact.out : (D.ntw.l i).Prime).ne_zero h3

theorem gOk_local (i : D.ntw.Tw) (k : ℕ) (y : D.ntw.O0 i) (hy : y ∈ maximalIdeal (D.ntw.O0 i)) :
    gOk D i k y ∈ maximalIdeal (D.ntw.Ok i k) := by
  have h1 := map_mem_maximalIdeal (algebraMap (D.ntw.O0 i) (D.ntw.O i)) (D.ntw.l i) (l_ne_zero D i) (D.ntw.O_l i) y hy
  have := D.ntw.Ok_fin i k
  have hint : (algebraMap (D.ntw.O i) (D.ntw.Ok i k)).IsIntegral :=
    algebraMap_isIntegral_iff.mpr inferInstance
  have hloc := hint.isLocalHom (D.ntw.Ok_inj i k)
  rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
  exact fun h => h1 (hloc.map_nonunit _ h)

def embAt (i : D.ntw.Tw) : D.what₂.LL →+* FractionRing (D.ntw.Ok i 1) :=
  (iotaOk D i 1).comp ((D.ntw.emb0 i).comp (toLL0 D hLL0))

theorem embAt_w (w : D.what₂.places.Pl) (i : D.ntw.Tw)
    (hi : ∀ x : 𝓞 ↥D.LL0, x ∈ (plLL0 D hLL0 (D.plEq w)).asIdeal ↔
      ∃ y ∈ maximalIdeal (D.ntw.O0 i),
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔
      embAt D hLL0 i x ∈ (algebraMap (D.ntw.Ok i 1) (FractionRing (D.ntw.Ok i 1))).range := by
  rw [val_nonneg_iff]
  refine val_le_one_iff (D.plEq w) (IsFractionRing.injective _ _) (embAt D hLL0 i) ?_ ?_ x
  · intro a ha
    have h1 : psiO D hLL0 a ∈ (plLL0 D hLL0 (D.plEq w)).asIdeal := by
      show phiO D (psiO D hLL0 a) ∈ (D.plEq w).asIdeal
      rw [phi_psi]; exact ha
    obtain ⟨y, hy, hy'⟩ := (hi _).1 h1
    refine ⟨gOk D i 1 y, gOk_local D i 1 y hy, ?_⟩
    rw [← iotaOk_alg, hy']
    rfl
  · intro a ha
    have h1 : psiO D hLL0 a ∉ (plLL0 D hLL0 (D.plEq w)).asIdeal := by
      show ¬ phiO D (psiO D hLL0 a) ∈ (D.plEq w).asIdeal
      rw [phi_psi]; exact ha
    have hint : IsIntegral (D.ntw.O0 i) (D.ntw.emb0 i ((psiO D hLL0 a : 𝓞 ↥D.LL0) : ↥D.LL0)) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom (D.ntw.O0 i)) (D.ntw.emb0 i) (RingHom.ext_int _ _)
        (RingOfIntegers.isIntegral_coe (psiO D hLL0 a))
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hu : IsUnit y := by
      by_contra hn
      exact h1 ((hi _).2 ⟨y, (mem_maximalIdeal y).2 hn, hy⟩)
    refine ⟨(hu.map (gOk D i 1)).unit, ?_⟩
    rw [IsUnit.unit_spec, ← iotaOk_alg, hy]
    rfl

def embAtB (i : D.ntw.Tw) : D.what₂.LL →+* FractionRing (D.ntw.Ok i 1) :=
  (iotaOk D i 1).comp ((D.ntw.emb0b i).comp (toLL0 D hLL0))

theorem embAtB_eq (i : D.ntw.Tw) (x : D.what₂.LL) : embAtB D hLL0 i x = embAt D hLL0 i (star x) :=
  congrArg (iotaOk D i 1) (D.ntw.restX_coefficientEmbedding_conj i (toLL0 D hLL0 x) (toLL0 D hLL0 (star x)) rfl)

def repW (w : D.what₂.places.Pl) : D.what₂.places.Pl :=
  @Classical.epsilon _ ⟨w⟩ (fun v => v = w ∨ v = D.what₂.places.conj w)

theorem repW_spec (w : D.what₂.places.Pl) : repW D w = w ∨ repW D w = D.what₂.places.conj w :=
  @Classical.epsilon_spec _ (fun v => v = w ∨ v = D.what₂.places.conj w) ⟨w, Or.inl rfl⟩

theorem repW_conj (w : D.what₂.places.Pl) : repW D (D.what₂.places.conj w) = repW D w := by
  unfold repW
  congr 1
  funext v
  rw [D.what₂.places.conj_conj]
  exact propext or_comm

theorem resChar_conj' (w : D.what₂.places.Pl) :
    D.what₂.places.resChar (D.what₂.places.conj w) = D.what₂.places.resChar w := by
  have hp := D.what₂.places.resChar_prime w
  have hq := D.what₂.places.resChar_prime (D.what₂.places.conj w)

  have h1 : (0 : WithTop ℤ) < D.what₂.places.val (D.what₂.places.conj w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.conj_val, star_natCast, D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have h2 : (0 : WithTop ℤ) < D.what₂.places.val (D.what₂.places.conj w)
      ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos _
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  have h3 : (1 : D.what₂.LL) = (a : D.what₂.LL) * ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL) +
      (b : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    have := congrArg (fun z : ℤ => (z : D.what₂.LL)) hab
    push_cast at this
    exact this.symm
  have hint : ∀ z : ℤ, (0 : WithTop ℤ) ≤ D.what₂.places.val (D.what₂.places.conj w) (z : D.what₂.LL) := fun z => by
    rw [val_nonneg_iff]
    have := (D.plEq (D.what₂.places.conj w)).valuation_le_one (K := D.what₂.LL) (z : 𝓞 D.what₂.LL)
    simpa using this
  have h4 : (0 : WithTop ℤ) < D.what₂.places.val (D.what₂.places.conj w) (1 : D.what₂.LL) := by
    rw [h3]
    refine lt_of_lt_of_le ?_ (AddValuation.map_add _ _ _)
    rw [lt_min_iff, AddValuation.map_mul, AddValuation.map_mul]
    exact ⟨lt_of_lt_of_le h2 (le_add_of_nonneg_left (hint a)), lt_of_lt_of_le h1 (le_add_of_nonneg_left (hint b))⟩
  rw [AddValuation.map_one] at h4
  exact lt_irrefl _ h4

open Classical in

def nchEmbOf (hc : NTw.TwCover D.ntw) : NChEmb D where
  twI := fun w => (cover_at D hLL0 hc (repW D w)).choose
  twI_l := fun w => by
    rw [(cover_at D hLL0 hc (repW D w)).choose_spec.1]
    rcases repW_spec D w with h | h
    · rw [h]
    · rw [h, resChar_conj']
  sd := fun w => decide (repW D w = w)
  embW := fun w => if repW D w = w then embAt D hLL0 _ else embAtB D hLL0 _
  embW_w := fun w x => by
    by_cases h : repW D w = w
    · rw [if_pos h]
      have := embAt_w D hLL0 (repW D w) _ (cover_at D hLL0 hc (repW D w)).choose_spec.2 x
      have e : D.what₂.places.val (repW D w) x = D.what₂.places.val w x := by rw [h]
      rw [e] at this
      exact this
    · rw [if_neg h, embAtB_eq]
      have h' : repW D w = D.what₂.places.conj w := (repW_spec D w).resolve_left h
      have := embAt_w D hLL0 (repW D w) _ (cover_at D hLL0 hc (repW D w)).choose_spec.2 (star x)
      have e : D.what₂.places.val (repW D w) (star x) = D.what₂.places.val w x := by
        rw [h', D.conj_val, star_star]
      rw [e] at this
      exact this

end Formalism.MainNotions.Inhab

end
end

