import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.HermitianColumns.Bundle0004
import Formalism.LocalToGlobal.Columns.DecoFin
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NoRamifiedNorm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ErrTies

theorem trace_rat {R : Ranks} (H : Host R) (x : H.E) (hx : x ∈ H.K) :
    ∃ r : ℚ, (r : H.E) = x + H.conj x := by
  have h1 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x, hx⟩
  have h2 := Formalism.MainNotions.UnusedSlot33.HK.norm_K H ⟨x + 1, add_mem hx (one_mem _)⟩
  refine ⟨Algebra.norm ℚ (⟨x + 1, add_mem hx (one_mem _)⟩ : H.K) -
    Algebra.norm ℚ (⟨x, hx⟩ : H.K) - 1, ?_⟩
  rw [eq_ratCast] at h1 h2
  push_cast
  rw [h1, h2]
  simp only [map_add, map_one]
  ring

theorem no_ramified_norm {T d : ℕ} (hT : T.Prime) (hd : d.Prime) (h2 : T ≠ 2) (hTd : T ≠ d)
    (a : ℤ) (s : ℚ) (h : ((T : ℚ) * a) ^ 2 - 4 * T = -d * s ^ 2) : False := by
  have hTZ : Prime (T : ℤ) := Nat.prime_iff_prime_int.1 hT
  have hq : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have hs : s * s.den = s.num := Rat.mul_den_eq_num s
  have hZ : (T : ℤ) * ((T * a ^ 2 - 4) * (s.den : ℤ) ^ 2) = -d * s.num ^ 2 := by
    have : (T : ℚ) * ((T * a ^ 2 - 4) * (s.den : ℚ) ^ 2) = -d * (s.num : ℚ) ^ 2 := by
      rw [← hs]
      linear_combination (s.den : ℚ) ^ 2 * h
    exact_mod_cast this
  have hnd : ¬ (T : ℤ) ∣ -(d : ℤ) := by
    rw [dvd_neg, Int.natCast_dvd_natCast]
    exact fun h => hTd ((Nat.prime_dvd_prime_iff_eq hT hd).1 h)
  have hp : (T : ℤ) ∣ s.num :=
    hTZ.dvd_of_dvd_pow ((hTZ.dvd_or_dvd ⟨_, hZ.symm⟩).resolve_left hnd)
  obtain ⟨p, hp'⟩ := hp
  have hT0 : (T : ℤ) ≠ 0 := hTZ.ne_zero
  have hZ2 : (T * a ^ 2 - 4) * (s.den : ℤ) ^ 2 = T * (-d * p ^ 2) := by
    apply mul_left_cancel₀ hT0
    rw [hZ, hp']; ring
  have h4 : (T : ℤ) ∣ 2 ^ 2 * (s.den : ℤ) ^ 2 :=
    ⟨a ^ 2 * (s.den : ℤ) ^ 2 + d * p ^ 2, by linear_combination -hZ2⟩
  rcases hTZ.dvd_or_dvd h4 with h5 | h5
  · have h6 : (T : ℤ) ∣ ((2 : ℕ) : ℤ) := hTZ.dvd_of_dvd_pow h5
    rw [Int.natCast_dvd_natCast] at h6
    exact h2 ((Nat.prime_dvd_prime_iff_eq hT Nat.prime_two).1 h6)
  · have h6 : T ∣ s.den := Int.natCast_dvd_natCast.1 (hTZ.dvd_of_dvd_pow h5)
    have h7 : T ∣ s.num.natAbs := Int.natCast_dvd.1 ⟨p, hp'⟩
    have h8 := Nat.dvd_gcd h7 h6
    rw [s.reduced] at h8
    exact hT.one_lt.ne' (Nat.dvd_one.1 h8)

theorem not_both_mem {R : Ranks} (H : Host R) {T : ℕ} (hT : T.Prime) (π π' : 𝓞 H.E)
    (hK : (π : H.E) ∈ H.K) (hc : (π' : H.E) = H.conj π) (hN : (π : H.E) * H.conj π = T)
    (M : ℕ) (hM : 2 * H.d ∣ M) (hcong : π - 1 ∈ Ideal.span {(M : 𝓞 H.E)})
    (P : Ideal (𝓞 H.E)) (hP : P ≠ ⊤) (h1 : π ∈ P) (h2 : π' ∈ P) : False := by
  have hTe : π * π' = (T : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    push_cast
    rw [← hN, ← hc]
  have hTP : (T : 𝓞 H.E) ∈ P := hTe ▸ P.mul_mem_right _ h1
  have hTM : ¬ T ∣ M := by
    rintro ⟨k, hk⟩
    apply hP
    rw [Ideal.eq_top_iff_one]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hcong
    have : (1 : 𝓞 H.E) = π - c * k * T := by
      rw [hk] at hc
      push_cast at hc
      linear_combination hc
    rw [this]
    exact P.sub_mem h1 (P.mul_mem_left _ hTP)
  have hT2 : T ≠ 2 := fun h => hTM (h ▸ (Dvd.intro _ rfl).trans hM)
  have hTd : T ≠ H.d := fun h => hTM (h ▸ (Dvd.intro_left _ rfl).trans hM)
  obtain ⟨r, hr⟩ := trace_rat H π hK
  have hint : IsIntegral ℤ r := by
    have : IsIntegral ℤ (algebraMap ℚ H.E r) := by
      rw [eq_ratCast, hr, ← hc]
      exact π.isIntegral_coe.add π'.isIntegral_coe
    exact (isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective).1 this
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [eq_intCast] at ha
  have haE : (a : 𝓞 H.E) = π + π' := by
    apply RingOfIntegers.ext
    push_cast
    rw [← ha] at hr
    push_cast at hr
    rw [← hc] at hr
    exact (map_intCast (algebraMap (𝓞 H.E) H.E) a).trans hr
  have hTa : (T : ℤ) ∣ a := by
    by_contra hn
    have hcop : IsCoprime (T : ℤ) a :=
      ((Nat.prime_iff_prime_int.1 hT).irreducible.coprime_iff_not_dvd).2 hn
    obtain ⟨x, y, hxy⟩ := hcop
    apply hP
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 H.E) = x * T + y * (π + π') := by
      rw [← haE]
      exact_mod_cast (congrArg (fun z : ℤ => (z : 𝓞 H.E)) hxy).symm
    rw [this]
    exact P.add_mem (P.mul_mem_left _ hTP) (P.mul_mem_left _ (P.add_mem h1 h2))
  obtain ⟨a', rfl⟩ := hTa
  set b := H.sqd with hb
  have hb0 : b ≠ 0 := Formalism.MainNotions.UnusedSlot33.HK.b_ne_zero H
  have hb2 : b ^ 2 = -(H.d : H.E) := Examples₂.bE_sq H
  have hbc : H.conj b = -b := Examples₂.conj_bE H
  obtain ⟨s, hs⟩ := trace_rat H ((π : H.E) / b) (div_mem hK (Formalism.MainNotions.UnusedSlot33.HK.bE_mem H))
  rw [map_div₀, hbc] at hs
  have hs' : (s : H.E) * b = π - H.conj π := by
    rw [hs]; field_simp; ring
  refine no_ramified_norm hT H.hyp.2.1 hT2 hTd a' s ?_
  have hE : (((T : ℚ) * a') ^ 2 - 4 * T : ℚ) = ((-(H.d : ℚ) * s ^ 2 : ℚ) : H.E) := by
    rw [← ha] at hr
    push_cast at hr ⊢
    rw [hr, ← hN, ← hb2]
    linear_combination (-((s : H.E) * b) - (π - H.conj π)) * hs'
  exact_mod_cast hE

theorem embLL_tauLL (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    D.what₂.embLL (tauLL D τ x) = D.host.emb (D.eTau τ).1 x := by
  rw [tauLL, Host.emb, ← D.embE_φ₀]
  rfl

def errOfTies (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : ErrX D where
  piG := (H.levelZeroCompatibility D.u₀).piG
  piG_K := (H.levelZeroCompatibility D.u₀).piG_K
  piG_norm i := by rw [← Examples₂.star_eq_conj]; exact (H.levelZeroCompatibility D.u₀).piG_norm i
  piT u := (H.atT u).piU
  piT_K u := (H.atT u).piU_K
  piT_norm u := (H.atT u).piU_norm
  piT_cong u := (H.atT u).piU_cong
  vPl u v := (H.base.vT u v).1
  vPl_inj u := fun _ _ h => (H.base.vT u).injective (Subtype.ext h)
  norm_mem_place_ideal u v := (H.base.vT u v).2

theorem seenDef (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : SeenDef D (errOfTies D H) := by
  intro u w hw
  obtain ⟨v⟩ : Nonempty (D.mem u).A.vT := by
    letI := (D.mem u).A.vTFin
    rw [← Fintype.card_pos_iff, (D.mem u).A.card_vT]
    unfold Ranks.f Ranks.n
    positivity
  have hτ : ∀ τ, tauLL D τ ((H.atT u).piU : D.host.E) = D.embE ((H.atT u).piU : D.host.E) := by
    intro τ
    rw [tauLL, Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K D.host _ (D.eTau τ).2 _ (H.atT u).piU_K]
  have key := (H.atT u).seen w hw v (H.atT u).piU _ (embLL_tauLL D _ _)
  rw [hτ] at key
  change _ ↔ ∀ τ, 0 < D.what₂.places.val w (tauLL D τ ((H.atT u).piU : D.host.E))
  simp only [hτ]
  constructor
  · intro hs _
    rw [if_pos hs] at key
    exact key.2 ((H.atT u).Pv_pi v)
  · intro h
    by_contra hs
    rw [if_neg hs, Formalism.L2.Col.mem_conjIdeal] at key
    refine not_both_mem D.host (D.mem u).A.T_prime (H.atT u).piU _ (H.atT u).piU_K ?_
      (H.atT u).piU_norm _ ?_ (H.atT u).piU_cong _ ((H.atT u).Pv_max v).ne_top
      ((H.atT u).Pv_pi v) (key.1 (h ((D.fm u).tauOf w v)))
    · exact Examples₂.star_eq_conj D.host _
    · obtain ⟨c, hc⟩ := D.host.two_dvd_QS
      refine ⟨c * D.host.q * (D.host.g 0 * D.host.g 1) ^ 2, ?_⟩
      trans D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2
      · ring
      · rw [hc]
        ring

theorem tauOfDef (D : D7) (H : Formalism.L2.Herm.ColsHermS D) : TauOfDef D (errOfTies D H) := by
  intro u w hw v x
  have key := (H.atT u).seen w hw v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) _ (embLL_tauLL D _ _)
  have hx : x ∈ (H.base.vT u v).1.asIdeal ↔
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ (H.atT u).Pv v := by
    rw [← (H.atT u).Pv_over v, Ideal.mem_comap]
  have hc : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    exact (Examples₂.star_eq_conj D.host _).trans ((Examples₂.conj_eq_self_iff D.host _).2 (x : D.host.F).2)
  refine hx.trans (Iff.trans ?_ key.symm)
  split_ifs
  · rfl
  · rw [Formalism.L2.Col.mem_conjIdeal, hc]

theorem exists_errX : ∀ (D : D7) (H : Formalism.L2.Herm.ColsHermS D), ∃ eX : ErrX D, eX.piG = (H.levelZeroCompatibility D.u₀).piG ∧ (∀ u, eX.piT u = (H.atT u).piU) ∧ (∀ u v, eX.vPl u v = (H.base.vT u v).1) ∧ PiGLevel D H.base.lev0 eX ∧ PiTLevel D H.base.lev0 eX ∧ SeenDef D eX ∧ TauOfDef D eX := by
  intro D H
  refine ⟨errOfTies D H, rfl, fun _ => rfl, fun _ _ => rfl, ?_, ?_, seenDef D H, tauOfDef D H⟩
  · intro u i v h
    have := (H.levelZeroCompatibility u).splitG_pi i v h
    rw [H.piG u D.u₀, Examples₂.star_eq_conj] at this
    exact this
  · intro u v z hz y
    exact (H.levelZeroCompatibility u).fM_pi _ _ z hz y

end GlobalTheory.Mem.ErrTies
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosIffSideMemMax
section
noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem pos_iff_side_mem_max {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0)
    (e : ↥D.LL0 →+* FractionRing (D.ntw.O0 (c.twI w)))
    (he : e = if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) :
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y = e (x : ↥D.LL0) := by
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (e (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) e (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = e (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have e1 := h.embedding_baseField_condition w x y 1 one_ne_zero (by rw [← he, map_one, mul_one, hy])
  simp only [map_one, mul_one] at e1
  rw [hleft, GlobalTheory.TwistGoodCompare.pos_iff_not_isUnit c w _ _ e1, not_iff_not]
  exact ⟨GlobalTheory.TwistGoodCompare.isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩

theorem resChar_eq_of_pos {D : D7} (w : D.what₂.places.Pl) {p : ℕ} (hp : p.Prime)
    (h : 0 < D.what₂.places.val w ((p : ℕ) : D.what₂.LL)) : D.what₂.places.resChar w = p := by
  by_contra hne
  have hq := D.what₂.places.resChar_prime w
  have hq0 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar w]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have hnat : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (D.what₂.places.val w).map_le_add ih (by simp)
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa using hnat m
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hnat m
  have h1 : (a : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) + (b : D.what₂.LL) * ((p : ℕ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) hab
  have h2 : 0 < D.what₂.places.val w 1 := by
    rw [← h1]
    refine (D.what₂.places.val w).map_lt_add ?_ ?_
    · rw [AddValuation.map_mul]; exact hq0.trans_le (le_add_of_nonneg_left (hint a))
    · rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b))
  simp at h2

theorem twCoverPair_of_tie (D : D7) (c : NChoice D) (h : NChTie D c) : TwCoverPair D := by
  rintro p hp w hw ⟨w', -, hw'⟩
  refine ⟨c.twI w', ?_, ?_⟩
  · rw [c.twI_l]
    refine resChar_eq_of_pos w' hp ?_
    simpa using (hw' _).1 hw
  · cases hs : c.sd w'
    · exact Or.inr fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_neg (by simp)]))
    · exact Or.inl fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_pos rfl]))

end GlobalTheory.Mem.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.Fld.RaySize

theorem isEmpty_realEmb (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : IsEmpty (E →+* ℝ) := by
  refine ⟨fun ψ => ?_⟩
  have h : InfinitePlace.IsReal (InfinitePlace.mk (Complex.ofRealHom.comp ψ)) :=
    ⟨_, ComplexEmbedding.isReal_iff.2 (by ext x; simp [ComplexEmbedding.conjugate]), rfl⟩
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h

theorem degOver_le_and_sz : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (φ : E →+* ℂ) (N : ℕ) (M : IntermediateField ℚ ℂ) (h : IsRayFieldIn φ (natIdeal E N) M), N ≠ 0 → degOver φ M h.emb_mem ≤ classNumber E * N ^ Module.finrank ℚ E ∧ Sz M (Real.log (Module.finrank ℚ E) + Real.log (degOver φ M h.emb_mem)) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log N + Real.log (degOver φ M h.emb_mem)) := by
  intro E _ _ _ φ N M h hN
  haveI : NumberField M := h.numberField
  letI := algOf φ M h.emb_mem
  have hR : IsRayField E M (natIdeal E N) := h.isRayField
  haveI : IsAbelianGalois E M := hR.1
  have hdeg : degOver φ M h.emb_mem = Module.finrank E M := rfl
  have hfin := finrank_mul_degOver φ M h.emb_mem
  rw [hdeg] at hfin ⊢
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.FieldSize.RayDegree.finrank_le E M (natIdeal E N) (natIdeal_ne_bot hN) hR.2
    haveI := isEmpty_realEmb E
    rwa [Fintype.card_eq_zero, pow_zero, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h1
  · refine ⟨inferInstance, ?_, ?_⟩
    · rw [← hfin]
      have : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
      have : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    · have hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 E), (N : 𝓞 E) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn M 𝔭 :=
        fun 𝔭 h𝔭 => hR.2.1 𝔭 (fun hd => h𝔭 (Ideal.dvd_span_singleton.1 hd))
      have hmem := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal E M N (Nat.pos_of_ne_zero hN) hun
      have h2 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal E M (N * Module.finrank E M)
        (Nat.mul_pos (Nat.pos_of_ne_zero hN) Module.finrank_pos) hmem
      have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hd : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul hN'.ne' hd.ne', ← add_assoc] at h2
      exact h2

end GlobalTheory.Mem.Fld.RaySize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TwFin

theorem exists_over {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremFour.main
  | exact _root_.GlobalTheory.IsolatedTheoremFour.main
  | (apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremFour.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremFour.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremFour.main ..)

theorem finite_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_span_singleton]
  exact hv

theorem mul_ne_one {R : Ranks} {H : Formalism.BasicNotions.Host R} {S : Set ℕ} {p : ℕ} {δ ψ : HChar H.E} (hp : p.Prime) (hS : p ∈ S)
    (hδ : IsDelta (H := H) p δ) (hψ : Chr.IsTwist H S ψ) : δ * ψ ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := exists_over (K := H.E) hp
  have hu : ψ.UnrAt v := by
    by_contra hn
    obtain ⟨-, hq, -, hnS⟩ := hψ.2.2.2 v hn
    have := Examples₂.PlacesToy.prime_mem_unique v hq hp (Ideal.absNorm_mem _) hv
    exact hnS (this ▸ hS)
  have h1 := (hδ.ine v hv 1).1 fun x hx => by
    have h2 : (δ * ψ).loc v x = 1 := by rw [h, HChar.loc_one]
    rw [HChar.loc_mul, hu x hx, mul_one] at h2
    rw [h2, one_pow]
  omega

theorem resChar_conj (B : Base) (w : B.places.Pl) : B.places.resChar (B.places.conj w) = B.places.resChar w := by
  refine Examples₂.PlacesToy.prime_mem_unique (B.places.conj w) (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) ?_
  have h := (Examples₂.PlacesToy.mem_conjW_pow w ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 B.LL) 1).2
    (by rw [pow_one, map_natCast]; exact Examples₂.PlacesToy.resCharW_mem w)
  rw [pow_one] at h
  exact h

theorem finite_pl (B : Base) (s : Finset ℕ) : {w : B.places.Pl | B.places.resChar w ∈ s}.Finite := by
  refine ((s.finite_toSet.subset (s := (s : Set ℕ)) (t := {p | p ∈ s ∧ p ≠ 0}) fun p hp => hp.1).biUnion
    fun p hp => finite_mem (K := B.LL) hp.2).subset fun w hw => ?_
  simp only [Set.mem_iUnion]
  exact ⟨B.places.resChar w, ⟨hw, (B.places.resChar_prime w).ne_zero⟩, Examples₂.PlacesToy.resCharW_mem w⟩

theorem tw_fin : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B), (T.set f).Finite ∧ (∀ w, T.xiTw f w ≠ 1) ∧ (∀ w, T.xiTw f (B.places.conj w) = T.xiTw f w) ∧ {w : B.places.Pl | B.places.resChar w ∈ T.pl}.Finite := by
  intro B f T
  refine ⟨?_, fun w => ?_, fun w => ?_, finite_pl B T.pl⟩
  · have h3 : ({1, f.del, f.del'} : Set (HChar B.host.E)).Finite := Set.toFinite _
    refine (h3.union ((finite_pl B T.pl).image (T.xiTw f))).subset ?_
    rintro ξ (h | ⟨w, rfl⟩)
    · exact Or.inl h
    · by_cases hw : B.places.resChar w ∈ T.pl
      · exact Or.inr ⟨w, hw, rfl⟩
      · left
        unfold TwDat.xiTw
        rw [(T.off w hw).1, mul_one]
        split_ifs
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
  · unfold TwDat.xiTw
    split_ifs
    · exact mul_ne_one B.host.pde'_prime (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) f.isDel' (T.psi_tw w)
    · exact mul_ne_one B.host.pde_prime (Or.inr (Or.inr (Or.inl rfl))) f.isDel (T.psi_tw w)
  · unfold TwDat.xiTw
    rw [resChar_conj, (T.conj w).1]

end GlobalTheory.Mem.Top.TwFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizesEqCount
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.Top

def duPre (B : Pre) (u : B.Word) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.k) (StandardLattice.stdLat B.host.E B.R.k)) *
    (StandardLattice.idxColLoc (B.host.g 0) B.R.k ^ B.R.f * StandardLattice.idxColLoc (B.host.g 1) B.R.k ^ B.R.f) *
    ∏ τ : Tau B.R, StandardLattice.dimV (fun i : Fin B.R.k => (((B.hcW u τ).u i : ℚ) : ℝ))

def DsPre (B : Pre) : ℝ :=
  (letI := B.host.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm B.host.E B.R.r) (StandardLattice.stdLat B.host.E B.R.r)) *
    (StandardLattice.idxRowLoc (B.host.g 0) B.R.k B.R.m ^ B.R.f * StandardLattice.idxRowLoc (B.host.g 1) B.R.k B.R.m ^ B.R.f) *
    ∏ τ : Tau B.R, Vol.trueDsig B.R (B.hc τ)

theorem Ctx.Over.sizes {K : Ctx} {B : Pre} (h : K.Over B) :
    (∀ u, (B.duStar u : ℝ) = duPre B u) ∧ B.Dstar = DsPre B := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  exact ⟨fun u => K.du_eq u, K.Ds_eq⟩

theorem sigYD_zero (R : Ranks) : 2 ≤ (sigYD R 0).1 ∧ (sigYD R 0).1 + (sigYD R 0).2 = R.r := by
  have h1 := R.two_le_m
  have h2 := R.m_add_three_le_k
  simp only [sigYD, Ranks.rankY, Ranks.r]
  omega

theorem sizes_eq_count (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre) (hv : StandardLattice.VolumeEqMass₂ X.toD7)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    (∀ u, ((X.toD7.mem u).A.duStar : ℝ) = StandardLattice.duStarU X.toD7 u) ∧ X.toD7.what₂.Dstar = StandardLattice.DstarD X.toD7 := by
  obtain ⟨h1, h2⟩ := hO.sizes
  refine ⟨fun u => ?_, ?_⟩
  · have e : (X.toD7.mem u).A.duStar = X.B.duStar u := X.C.A_duStar u
    rw [e]
    refine (h1 u).trans ?_
    unfold duPre StandardLattice.duStarU StandardLattice.duStarP
    congr 1
  · have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
    rw [e, h2]
    have hvol : StandardLattice.volY0 X.toD7 = StandardLattice.massI X.toD7 X.B.R.r := by
      letI := X.toD7.host.cmStar
      have := hv.2 (X.toD7.sp.Y 0) (sigYD X.B.R 0).1 (sigYD X.B.R 0).2 (X.toD7.sp.Y_sig 0)
        (fun τ => X.toD7.Y_sigval 0 (Nat.zero_le _) τ) (sigYD_zero _).1
      rw [(sigYD_zero _).2] at this
      exact this
    unfold DsPre StandardLattice.DstarD StandardLattice.DstarP
    rw [hvol]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

end GlobalTheory.Mem.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice : ∀ (D : _root_.Formalism.BasicNotions.D7) (c : _root_.Formalism.BasicNotions.NChoice D),
    _root_.Formalism.BasicNotions.NChTie D c → IsGalois ℚ ↥D.LL0 →
    ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → D.ntw.NonzeroIndexPlace (c.twI w) := by
  intro D c hc hG w hw
  unfold _root_.Formalism.BasicNotions.NTw.NonzeroIndexPlace
  refine ⟨if c.sd w = true then w else D.what₂.places.conj w, ?_, ?_⟩
  · split_ifs
    · exact hw
    · rw [_root_.Formalism.BasicNotions.Rows.Data.muAt_conj]
      exact hw
  · have h := _root_.GlobalTheory.TwistGoodCompare.liesUnder_of_tie hG hc w
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder at h
    exact h

end GlobalTheory.Mem.Top
end

