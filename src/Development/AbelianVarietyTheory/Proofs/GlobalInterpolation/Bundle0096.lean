import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0035
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0084
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexEqOfSelfDualAlternating
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.DualCount

theorem relIndex_le_of_selfDual (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hanti : ∀ x y, ω x y = -ω y x)
    (h₁ : ∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n)
    (h₂ : ∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n)
    (hfin : Λ₁.relIndex Λ₂ ≠ 0) : Λ₂.relIndex Λ₁ ≤ Λ₁.relIndex Λ₂ := by
  classical
  have hadd' : ∀ x y z, ω x (y + z) = ω x y + ω x z := by
    intro x y z
    rw [hanti x (y + z), hadd, hanti x y, hanti x z]; ring
  have hsub : ∀ x y z, ω (x - y) z = ω x z - ω y z := by
    intro x y z
    have := hadd (x - y) y z
    rw [sub_add_cancel] at this
    linarith
  have hint : ∀ r : ℝ, ((r : ℝ) : UnitAddCircle) = 0 ↔ ∃ n : ℤ, r = n := by
    intro r
    rw [AddCircle.coe_eq_zero_iff]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by simpa using hn.symm⟩
  let φ : H → (Λ₂ →+ UnitAddCircle) := fun x =>
    AddMonoidHom.mk' (fun y => ((ω x y : ℝ) : UnitAddCircle)) (by
      intro a b
      simp only [AddSubgroup.coe_add, hadd', AddCircle.coe_add])
  have hφ : ∀ x : Λ₁, Λ₁.addSubgroupOf Λ₂ ≤ (φ x).ker := by
    intro x y hy
    rw [AddMonoidHom.mem_ker]
    exact (hint _).2 ((h₁ x).1 x.2 y (AddSubgroup.mem_addSubgroupOf.1 hy))
  let ψ : Λ₁ → (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ →+ UnitAddCircle) := fun x =>
    QuotientAddGroup.lift _ (φ x) (hφ x)
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let χ : Λ₁ → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) Circle := fun x =>
    (AddCircle.toCircle_addChar (T := 1)).compAddMonoidHom (ψ x)
  have hχ : ∀ a b : Λ₁, χ a = χ b → ((a : H) - b) ∈ Λ₂ := by
    intro a b hab
    rw [h₂]
    intro y hy
    have h := DFunLike.congr_fun hab (QuotientAddGroup.mk ⟨y, hy⟩)
    have h' : AddCircle.toCircle (((ω a y : ℝ)) : UnitAddCircle)
        = AddCircle.toCircle (((ω b y : ℝ)) : UnitAddCircle) := h
    have h'' := AddCircle.injective_toCircle (T := 1) one_ne_zero h'
    rw [← hint, hsub, AddCircle.coe_sub, h'', sub_self]
  haveI hG : Finite (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Nat.finite_of_card_ne_zero hfin
  haveI : Fintype (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := Fintype.ofFinite _
  let f : (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) → AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ := fun q =>
    AddChar.circleEquivComplex (χ q.out)
  have hf : Function.Injective f := by
    intro p q hpq
    have h := hχ _ _ (AddChar.circleEquivComplex.injective hpq)
    rw [← QuotientAddGroup.out_eq' p, ← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem,
      AddSubgroup.mem_addSubgroupOf]
    exact h
  have hle := Nat.card_le_card_of_injective f hf
  have hc : Nat.card (AddChar (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ℂ)
      = Nat.card (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  rw [hc] at hle
  exact hle

theorem relIndex_eq_of_selfDual : ∀ (H : Type) [AddCommGroup H] (ω : H → H → ℝ)
    (Λ₁ Λ₂ : AddSubgroup H), (∀ x y z, ω (x + y) z = ω x z + ω y z) → (∀ x y, ω x y = -ω y x) →
    (∀ x, x ∈ Λ₁ ↔ ∀ y ∈ Λ₁, ∃ n : ℤ, ω x y = n) → (∀ x, x ∈ Λ₂ ↔ ∀ y ∈ Λ₂, ∃ n : ℤ, ω x y = n) →
    Λ₁.relIndex Λ₂ ≠ 0 → Λ₂.relIndex Λ₁ ≠ 0 → Λ₁.relIndex Λ₂ = Λ₂.relIndex Λ₁ := by
  intro H _ ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁ f₂
  exact le_antisymm (relIndex_le_of_selfDual H ω Λ₂ Λ₁ hadd hanti h₂ h₁ f₂)
    (relIndex_le_of_selfDual H ω Λ₁ Λ₂ hadd hanti h₁ h₂ f₁)

end GlobalTheory.MomT.DualCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexMulVec
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.IdxDet

open GlobalTheory.LatBasisAt

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_mem (w : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt w a ↔ a ∈ locRing w := by
  rw [mem_locRing]
  constructor
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [← h]; field_simp⟩
  · rintro ⟨r, s, hs, h⟩
    have := algebraMap_ne_zero w hs
    exact ⟨r, s, hs, by rw [h]; field_simp⟩

theorem val_le_one (P : HeightOneSpectrum (𝓞 E)) (a : locRing P) : P.valuation E (a : E) ≤ 1 :=
  GlobalTheory.CharValCompare.intAt_iff.1 ((intAt_iff_mem P _).2 a.2)

theorem val_unit (P : HeightOneSpectrum (𝓞 E)) (u : (locRing P)ˣ) :
    P.valuation E ((u : locRing P) : E) = 1 := by
  have h : P.valuation E ((u : locRing P) : E) * P.valuation E (((u⁻¹ : (locRing P)ˣ) : locRing P) : E) = 1 := by
    rw [← map_mul, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one, map_one]
  refine le_antisymm (val_le_one P _) ?_
  rw [← h]
  exact mul_le_of_le_one_right' (val_le_one P _)

theorem val_irreducible (P : HeightOneSpectrum (𝓞 E)) [IsDiscreteValuationRing (locRing P)]
    {p : locRing P} (hp : Irreducible p) : P.valuation E (p : E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hπ1 : π ∈ locRing P := by
    rw [← intAt_iff_mem, GlobalTheory.CharValCompare.intAt_iff, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hπ0 : (⟨π, hπ1⟩ : locRing P) ≠ 0 := by
    intro h
    have : π = 0 := congrArg Subtype.val h
    rw [this, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hp
  have h1 : π * ((u : locRing P) : E) = (p : E) ^ k := by
    simpa using congrArg Subtype.val hu
  have h2 := congrArg (P.valuation E) h1
  rw [map_mul, val_unit, mul_one, hπ, map_pow] at h2
  have hp0 : P.valuation E (p : E) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact fun h => hp.ne_zero (Subtype.ext h)
  have hle := val_le_one P p
  rw [← WithZero.exp_log hp0] at h2 hle ⊢
  generalize WithZero.log (P.valuation E (p : E)) = a at h2 hle ⊢
  rw [← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h2
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  congr 1
  have : a ∣ 1 := ⟨-k, by linarith⟩
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one this) with h | h
  · omega
  · exact h

theorem relIndex_mulVec : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (P : HeightOneSpectrum (𝓞 E)) (M : Matrix ι ι E) (L₀ L₁ : AddSubgroup (ι → E)), M.det ≠ 0 → (∀ x, x ∈ L₀ ↔ ∀ i, IntAt P (x i)) → (∀ x, x ∈ L₁ ↔ ∃ y ∈ L₀, x = M.mulVec y) → L₁ ≤ L₀ → ((L₁.relIndex L₀ : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ ordE P M.det := by
  intro E _ _ ι _ _ P M L₀ L₁ hdet h0 h1 hle
  haveI := P.isPrime
  haveI := P.isMaximal
  haveI : IsDiscreteValuationRing (locRing P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot (locRing P)
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (locRing P)
  have hent : ∀ i j, M i j ∈ locRing P := by
    intro i j
    have hs : (Pi.single j 1 : ι → E) ∈ L₀ := by
      rw [h0]
      intro k
      rw [intAt_iff_mem, Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have := (h0 _).1 (hle ((h1 _).2 ⟨_, hs, rfl⟩)) i
    rw [intAt_iff_mem] at this
    simpa using this
  let N : Matrix ι ι (locRing P) := Matrix.of fun i j => ⟨_, hent i j⟩
  have hN : N.map (algebraMap (locRing P) E) = M := by
    ext i j; rfl
  have hNd : ((N.det : locRing P) : E) = M.det := by
    rw [← hN]
    exact RingHom.map_det (algebraMap (locRing P) E) N
  have hne : N.det ≠ 0 := by
    intro h
    rw [h] at hNd
    exact hdet hNd.symm
  have hinj : Function.Injective (Matrix.toLin' N) := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_toLin'_eq_bot_iff]
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hne hv
  obtain ⟨m, ⟨v, hv⟩, hc⟩ := GlobalTheory.HL.LatDet.card_coker (Pi.basisFun (locRing P) ι) hp _ hinj
  rw [LinearMap.det_toLin'] at hv
  have hord : ordE P M.det = m := by
    have e1 : M.det * ((v : locRing P) : E) = (p : E) ^ m := by
      rw [← hNd]; exact_mod_cast congrArg Subtype.val hv
    have e2 := congrArg (P.valuation E) e1
    rw [map_mul, val_unit, mul_one, map_pow, val_irreducible P hp, ← WithZero.exp_nsmul] at e2
    unfold ordE
    rw [e2, WithZero.log_exp]
    simp
  have hq : Nat.card (locRing P ⧸ Ideal.span {p}) = Ideal.absNorm P.asIdeal := by
    rw [← hp.maximalIdeal_eq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal P.asIdeal (locRing P)).toEquiv).symm
  let e : (ι → locRing P) →+ (ι → E) :=
    { toFun := fun x i => (x i : E)
      map_zero' := rfl
      map_add' := fun x y => rfl }
  have hei : Function.Injective e := by
    intro x y hxy
    funext i
    exact Subtype.ext (congrFun hxy i)
  have hW0 : L₀ = AddSubgroup.map e ⊤ := by
    ext x
    rw [h0]
    constructor
    · intro hx
      exact ⟨fun i => ⟨_, (intAt_iff_mem P _).1 (hx i)⟩, trivial, rfl⟩
    · rintro ⟨y, -, rfl⟩ i
      exact (intAt_iff_mem P _).2 (y i).2
  have hcomm : ∀ y, M.mulVec (e y) = e (Matrix.toLin' N y) := by
    intro y
    funext i
    rw [← hN]
    exact (RingHom.map_mulVec (algebraMap (locRing P) E) N y i).symm
  have hW1 : L₁ = AddSubgroup.map e (LinearMap.range (Matrix.toLin' N)).toAddSubgroup := by
    ext x
    rw [h1, hW0]
    constructor
    · rintro ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, (hcomm y).symm⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨_, ⟨y, trivial, rfl⟩, (hcomm y).symm⟩
  have : L₁.relIndex L₀ = Ideal.absNorm P.asIdeal ^ m := by
    rw [hW1, hW0, AddSubgroup.relIndex_map_map_of_injective _ _ hei, AddSubgroup.relIndex_top_right, ← hq]
    exact hc
  rw [this, hord, zpow_natCast, Nat.cast_pow]

end GlobalTheory.IdxDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexPerDvd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.IdxBound

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_of_locP {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (M : Submodule (𝓞 E) W) (x : W)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : ∀ s, s ∈ I ↔ s • x ∈ M := fun s => Iff.rfl
  have hne : I ≠ ⊤ := fun e => hx (by simpa using (hI 1).1 (e ▸ Submodule.mem_top))
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := (mem_locP ⟨m, hm.isPrime, hm0⟩ M x).1 (h _)
  exact hs (hle ((hI s).2 hsx))

theorem mem_localization_of_smul_mem {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) W)
    {x : W} {s : 𝓞 E} (hs : s ∉ P.asIdeal) (h : s • x ∈ localization₂ P.asIdeal M) : x ∈ localization₂ P.asIdeal M := by
  obtain ⟨t, ht, htx⟩ := (mem_locP P M _).1 h
  refine (mem_locP P M _).2 ⟨t * s, fun h' => (P.isPrime.mem_or_mem h').elim ht hs, ?_⟩
  rwa [mul_smul]

theorem per_apply_mem {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E))
    {y : HomE E a b} (hy : y ∈ perO AA N N') {v : Sp E a} (hv : v ∈ localization₂ P.asIdeal N) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s', hs', hv'⟩ := (mem_locP P N v).1 hv
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    obtain ⟨s, hs, hr'⟩ := (mem_locP P _ r).1 (hA ▸ le_locP P AA hr)
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hr'
    refine mem_localization_of_smul_mem P _ hs (mem_localization_of_smul_mem P _ hs' (le_locP P _ ?_))
    have h1 : x (s' • v) ∈ N' := hx _ hv'
    have h2 : s' • s • (r • x) v = t • x (s' • v) := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, ← smul_assoc s r, ← ht, algebraMap_smul, smul_comm]
    rw [h2]
    exact N'.smul_mem t h1
  | zero => simp
  | add y z _ _ hy hz => simpa using add_mem hy hz
  | smul r z _ hz => simpa using Submodule.smul_mem _ r hz

theorem mem_localization_perO {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (hN : N.FG)
    {y : HomE E a b} (hy : ∀ v ∈ N, y v ∈ localization₂ P.asIdeal N') : y ∈ localization₂ P.asIdeal (perO AA N N') := by
  classical
  obtain ⟨S, rfl⟩ := hN
  choose! s hs hsy using fun v (hv : v ∈ S) => (mem_locP P N' _).1 (hy v (Submodule.subset_span hv))
  have hP : ∏ v ∈ S, s v ∉ P.asIdeal := fun h => by
    obtain ⟨v, hv, h'⟩ := (P.isPrime.prod_mem_iff).1 h
    exact hs v hv h'
  have hh : (∏ v ∈ S, s v) • y ∈ homO (Submodule.span (𝓞 E) (S : Set (Sp E a))) N' := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rw [← Finset.prod_erase_mul S s hv, LinearMap.smul_apply, mul_smul]
      exact N'.smul_mem _ (hsy v hv)
    | zero => simp
    | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
    | smul r v _ hv => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem r hv
  obtain ⟨t, ht, h1⟩ := (mem_locP P AA 1).1 (hA ▸ le_locP P _ (Submodule.one_le.1 le_rfl))
  refine mem_localization_of_smul_mem P _ hP (mem_localization_of_smul_mem P _ ht (le_locP P _ (Submodule.subset_span ⟨_, h1, _, hh, ?_⟩)))
  rw [smul_assoc t (1 : E), one_smul]

theorem smul_mem_per {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' N'' : Submodule (𝓞 E) (Sp E b)}
    {w : 𝓞 E} (h : ∀ y ∈ N', (w : E) • y ∈ N'') {y : HomE E a b} (hy : y ∈ perO AA N N') : w • y ∈ perO AA N N'' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨r, hr, w • x, fun v hv => h _ (hx v hv), (smul_comm _ _ _).symm⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz

theorem apply_mem_of_std {N' : Submodule (𝓞 E) (Sp E b)} {P : HeightOneSpectrum (𝓞 E)} {y : HomE E a b}
    (hy : ∀ i, y (Pi.single i 1) ∈ localization₂ P.asIdeal N') {v : Sp E a} (hv : v ∈ stdAt E a P) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s, hs, hsv⟩ := (mem_locP P _ v).1 hv
  choose t ht using fun i => Submodule.mem_one.1 (Submodule.mem_pi.1 hsv i (Set.mem_univ _))
  refine mem_localization_of_smul_mem P _ hs ?_
  have e : s • v = ∑ i, t i • (Pi.single i 1 : Sp E a) := by
    ext j
    rw [← ht j]
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  rw [← LinearMap.map_smul_of_tower, e, map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ (hy i)

theorem relIndex_per_dvd : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (d : DecoSet X.E b (divs ϖ) SG) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → A.AAUnit (divs ϖ) → ϖ ≠ 0 → (∀ P ∈ divs ϖ, Ideal.absNorm P.asIdeal = p) → IsSdLat N → IsSdLat N'' → (∀ P ∈ divs ϖ, localization₂ P.asIdeal N = stdAt X.E a P) → ((∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0) → (per A N N'').toAddSubgroup.relIndex (per A N d.1.N).toAddSubgroup ∣ p ^ ((divs ϖ).card * a) := by
  intro X A a b SG ϖ p N d N'' _ _ hU h0 hp hN _ hstd ⟨h1, _, h3⟩
  have he : ∀ (P : ↥(divs ϖ)) (i : Fin a), (Pi.single i 1 : Sp X.E a) ∈ localization₂ P.1.asIdeal N := fun P i => by
    rw [hstd P.1 P.2]
    exact le_locP P.1 _ (by simpa using single_mem_stdLat (E := X.E) i 1)
  have hm : ∀ (x : (per A N d.1.N).toAddSubgroup) (P : ↥(divs ϖ)) (i : Fin a), x.1 (Pi.single i 1) ∈ d.1.at P.1 :=
    fun x P i => per_apply_mem (hU P.1 P.2) x.2 (he P i)
  let φ : (per A N d.1.N).toAddSubgroup →+ ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) :=
    AddMonoidHom.mk' (fun x P i => d.1.f P (x.1 (Pi.single i 1))) fun x y => by
      funext P i
      exact d.2.f_add P _ (hm x P i) _ (hm y P i)
  have hker : φ.ker ≤ (per A N N'').toAddSubgroup.addSubgroupOf (per A N d.1.N).toAddSubgroup := by
    intro x hx
    refine mem_of_locP (per A N N'') x.1 fun Q => ?_
    by_cases hQ : Q ∈ divs ϖ
    · refine mem_localization_perO (hU Q hQ) hN.1.fg fun v hv => apply_mem_of_std (fun i => ?_) (hstd Q hQ ▸ le_locP Q N hv)
      exact (h3 ⟨Q, hQ⟩ _).2 ⟨hm x ⟨Q, hQ⟩ i, congrFun (congrFun hx ⟨Q, hQ⟩) i⟩
    · exact mem_localization_of_smul_mem Q _ (fun h => hQ ((mem_divs h0 Q).2 h)) (le_locP Q _ (smul_mem_per h1 x.2))
  have hc : Nat.card ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ ((divs ϖ).card * a) := by
    have : ∀ P : ↥(divs ϖ), Nat.card (Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ a := fun P => by
      rw [Nat.card_fun, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hp P.1 P.2]
      simp
    rw [Nat.card_pi, Finset.prod_congr rfl fun P _ => this P]
    simp [← pow_mul, mul_comm]
  refine (AddSubgroup.index_dvd_of_le hker).trans ?_
  rw [AddSubgroup.index_ker, ← hc]
  exact AddSubgroup.card_addSubgroup_dvd_card _

end GlobalTheory.MomT.IdxBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
section
open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.Inh.ResFin

theorem infinite_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

theorem finite_residue {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (Q.valuation K).valuationSubring) := by
  let ι : 𝓞 K →+* (Q.valuation K).valuationSubring :=
    (algebraMap (𝓞 K) K).codRestrict (Q.valuation K).valuationSubring fun a => Q.valuation_le_one a
  have key : ∀ x : (Q.valuation K).valuationSubring,
      IsLocalRing.residue _ x = 0 ↔ Q.valuation K (x : K) < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  let φ : 𝓞 K ⧸ Q.asIdeal →+* IsLocalRing.ResidueField (Q.valuation K).valuationSubring :=
    Ideal.Quotient.lift Q.asIdeal ((IsLocalRing.residue _).comp ι) fun a ha => by
      rw [RingHom.comp_apply, key]
      exact (Q.valuation_lt_one_iff_mem (K := K) a).2 ha
  haveI : Finite (𝓞 K ⧸ Q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.ne_bot
  refine Finite.of_surjective φ fun y => ?_
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := Q.exists_valuation_sub_lt_of_integer (K := K) x.2 1
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  change IsLocalRing.residue _ (ι a) = _
  rw [← sub_eq_zero, ← map_sub, key]
  exact ha

def redHom {K k ι : Type} [Field K] [CommRing k] [Fintype ι] [DecidableEq ι] (O : Subring K) (φ : O →+* k)
    (G : Subgroup (GL ι K)) (hG : ∀ g ∈ G, IntGL O g) : G →* Matrix ι ι k where
  toFun g := Matrix.of fun a b => φ ⟨((g : GL ι K) : Matrix ι ι K) a b, (hG g g.2 a b).1⟩
  map_one' := by
    ext a b
    simp only [Matrix.of_apply, Matrix.one_apply, OneMemClass.coe_one, Units.val_one]
    split_ifs
    · exact map_one φ
    · exact map_zero φ
  map_mul' g h := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, ← map_mul, ← map_sum]
    congr 1
    apply Subtype.ext
    simp [Matrix.mul_apply]

end GlobalTheory.LvT.Inh.ResFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RhoVrBrAtEqBrStd
section
noncomputable section

namespace GlobalTheory.BranchBlock

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem isBlock_of_mulVec' {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {A' : Matrix (Fin N) (Fin N) E}
    {A : Matrix (Fin n) (Fin n) E} {c : E} (h1 : ∀ x, iniH hN (A' *ᵥ x) = A *ᵥ iniH hN x)
    (h2 : ∀ x, (A' *ᵥ x) (Br.iL hN) = c * x (Br.iL hN)) : BranchFormula.IsBlock hN A' A c := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h := congrFun (h1 (Pi.single (Br.iC hN b) 1)) a
    have e : iniH hN (Pi.single (Br.iC hN b) (1 : E)) = Pi.single b 1 := funext fun i => by
      simp only [iniH, Pi.single_apply, (Br.iC_inj hN).eq_iff]
    rw [e, mulVec_single_one, mulVec_single_one] at h
    exact h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rw [e, mulVec_single_one, mulVec_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rw [mulVec_single_one, Pi.single_eq_of_ne (hne a).symm, mul_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rw [mulVec_single_one, Pi.single_eq_same, mul_one] at h
    exact h

theorem rhoVr_brAt_eq_brStd : ∀ {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] (emb : ι → E →+* K) {N n : ℕ}
    (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Br.Interlace hN (lam τ) (sg τ)) →
    (∀ τ, Br.SameShift (lam τ) (sg τ)) → ∀ (t : E) (B' : GL (Fin n) E) (B : GL (Fin N) E),
    (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) →
    (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) →
    ∀ G : Formalism.L2.DIV.VV K lam, rhoVr emb sg B'⁻¹ (Br.brAt hN lam sg (fun τ => emb τ t) G) =
      Br.brStd hN lam sg (rhoVr emb lam B⁻¹ G) := by
  intro E K ι _ _ _ _ emb N n hN lam sg hI hS t B' B h1 h2 G
  have ht : t ≠ 0 := by
    intro h0
    have h := h2 (Pi.single (Br.iL hN) 1)
    rw [h0, zero_mul, Pi.single_eq_same] at h
    exact zero_ne_one h
  have hBA : ∀ x, (B : Matrix (Fin N) (Fin N) E) *ᵥ (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hAB : ∀ y, ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((B' : Matrix (Fin n) (Fin n) E) *ᵥ y) = y := by
    intro y
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hblk : BranchFormula.IsBlock hN ((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
      ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t := by
    refine isBlock_of_mulVec' hN (fun x => ?_) (fun x => ?_)
    · have h := h1 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      rw [h, hAB]
    · have h := h2 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      exact h.symm
  have e1 : ∀ {m : ℕ} (g : GL (Fin m) E) (τ : ι) (a b : Fin m),
      ((invTrK (embGL emb g) τ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) a b =
        emb τ (((g⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) b a) := fun g τ a b => rfl
  have key := BranchFormula.brAt_eq_pullback hN hI hS (invTrK (embGL emb B')) (invTrK (embGL emb B))
    (fun τ => emb τ t) (fun τ => (map_ne_zero _).2 ht) (fun τ => by
      refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp only [e1]
      · rw [hblk.1]
      · rw [(hblk.2.1 a).2, map_zero]
      · rw [(hblk.2.1 a).1, map_zero]
      · rw [hblk.2.2]) G
  show rhoK sg (invTrK (embGL emb B'⁻¹)) _ = Br.brStd hN lam sg (rhoK lam (invTrK (embGL emb B⁻¹)) G)
  rw [map_inv (embGL emb), map_inv (embGL emb), map_inv invTrK, map_inv invTrK]
  exact key.symm

end GlobalTheory.BranchBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeGSizeWordsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_sizeG_sizeWords : SzRow (fun _ _ L => SizeG L ∧ SizeWords L) := by
  first | exact @GlobalTheory.EX.szRow_sizeG_sizeWords | exact GlobalTheory.EX.szRow_sizeG_sizeWords | (intros; apply GlobalTheory.EX.szRow_sizeG_sizeWords <;> assumption)
end

