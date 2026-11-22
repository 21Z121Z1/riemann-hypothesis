import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import ReciprocityTheory.DualLattices.PowMemCarrier
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0025
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLat
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT

theorem inj_mod_of_surj_mod {M : Type} [AddCommGroup M] [Module.Finite ℤ M] (f : M →ₗ[ℤ] M) (q : ℕ)
    (hs : ∀ a, ∃ z b, a = f z + q • b) (z b : M) (h : f z = q • b) : ∃ z', z = q • z' := by
  let K : Submodule ℤ M := LinearMap.range (q • (LinearMap.id : M →ₗ[ℤ] M))
  have hK : ∀ a, a ∈ K ↔ ∃ b, a = q • b := fun a =>
    ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hle : K ≤ K.comap f := by
    intro a ha
    obtain ⟨b, rfl⟩ := (hK a).1 ha
    exact (hK _).2 ⟨f b, map_nsmul f q b⟩
  let g := K.mapQ K f hle
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨a, rfl⟩ := K.mkQ_surjective a
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨K.mkQ z, ?_⟩
    show K.mkQ (f z) = _
    rw [map_add, show K.mkQ (q • b) = 0 from (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, rfl⟩), add_zero]
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hg
  have h0 : g (K.mkQ z) = g 0 := by
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, h⟩)
  exact (hK z).1 ((Submodule.Quotient.mk_eq_zero K).1 (hi h0))

theorem surj_mod_pow {M L : Type} [AddCommGroup M] [AddCommGroup L] (σ : M →+ L) (p : ℕ)
    (h : ∀ a, ∃ z b, a = σ z + p • b) (n : ℕ) (a : L) : ∃ z b, a = σ z + (p ^ n) • b := by
  induction n with
  | zero => exact ⟨0, a, by simp⟩
  | succ n ih =>
    obtain ⟨z, b, rfl⟩ := ih
    obtain ⟨z', b', rfl⟩ := h b
    exact ⟨z + (p ^ n) • z', b', by rw [map_add, map_nsmul, smul_add, pow_succ, mul_smul, add_assoc]⟩

theorem perfect_mod {M L : Type} [AddCommGroup M] [AddCommGroup L] [Module.Free ℤ L] (σ : M →ₗ[ℤ] L) (q : ℕ)
    (EF : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (hE : Function.Bijective EF) (hs : ∀ a, ∃ z b, a = σ z + q • b)
    (hk : ∀ z b, σ z = q • b → ∃ z', z = q • z') :
    (∀ φ : M →+ ZMod q, ∃ y, ∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = φ z) ∧
      ∀ y, (∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = 0) → ∃ y', y = q • y' := by
  let B := Module.Free.chooseBasis ℤ L
  constructor
  · intro φ
    choose zz cc hzc using hs
    let s : L →ₗ[ℤ] M := B.constr ℤ fun i => zz (B i)
    let t : L →ₗ[ℤ] L := B.constr ℤ fun i => cc (B i)
    have hst : ∀ a, a = σ (s a) + q • t a := by
      have : (LinearMap.id : L →ₗ[ℤ] L) = σ ∘ₗ s + q • t := B.ext fun i => by
        simpa [s, t] using hzc (B i)
      intro a
      simpa using LinearMap.congr_fun this a
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => ((φ (zz (B i))).cast : ℤ)
    have hψ : ∀ a, ((ψ a : ℤ) : ZMod q) = φ (s a) := by
      have : (Int.castAddHom (ZMod q)).toIntLinearMap ∘ₗ ψ = φ.toIntLinearMap ∘ₗ s := B.ext fun i => by
        simp [ψ, s]
      intro a
      simpa using LinearMap.congr_fun this a
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine ⟨zz a₀, fun z => ?_⟩
    obtain ⟨z', hz'⟩ := hk (z - s (σ z)) (t (σ z)) (by
      rw [map_sub, sub_eq_iff_eq_add']
      exact hst (σ z))
    have h1 : φ z = φ (s (σ z)) := by
      rw [sub_eq_iff_eq_add.1 hz', map_add, map_nsmul]
      simp [← sub_eq_iff_eq_add.1 hz']
    have h2 : σ (zz a₀) = a₀ - q • cc a₀ := eq_sub_iff_add_eq.2 (hzc a₀).symm
    rw [h1, ← hψ, ← ha₀, h2]
    simp
  · intro y hy
    have hd : ∀ a, (q : ℤ) ∣ EF (σ y) a := by
      intro a
      obtain ⟨z, b, rfl⟩ := hs a
      rw [map_add, map_nsmul, nsmul_eq_mul]
      exact dvd_add ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hy z)) (dvd_mul_right _ _)
    choose d hd using hd
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => d (B i)
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine hk y a₀ (hE.1 (B.ext fun i => ?_))
    rw [map_nsmul, ha₀, hd]
    simp [ψ]

theorem exists_levPairing {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (p : ℕ) [Fact p.Prime] (n : ℕ)
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) {N : ℕ} (u : Fin N → La)
    (hu : IsPolLattice c p EF u) :
    ∃ (π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n)
      (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n)),
      (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) ∧
      (∀ z z', e z z' = ((EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) ∧
      (∀ a : La, ∃ (z : Fin N → 𝓞 E) (b : La), a = ∑ k, z k • u k + (p ^ n) • b) ∧
      Function.Surjective π ∧
      (∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ n) • y') ∧
      (∀ y, e y y = 0) ∧
      (∀ (a : 𝓞 E) (y z : Fin N → 𝓞 E), e (a • y) z = e y (RingOfIntegers.mapRingEquiv c a • z)) ∧
      (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ n), ∃ y, e y = φ) ∧
      (∀ y, e y = 0 → ∃ y', y = (p ^ n) • y') := by
  have := hu.free
  have := hu.finite
  let σ₀ : (Fin N → 𝓞 E) →ₗ[𝓞 E] La := Fintype.linearCombination (𝓞 E) u
  let σ : (Fin N → 𝓞 E) →ₗ[ℤ] La := σ₀.toAddMonoidHom.toIntLinearMap
  have hσ : ∀ z, σ z = ∑ k, z k • u k := fun z => Fintype.linearCombination_apply _ _ _
  have hσa : ∀ (a : 𝓞 E) z, σ (a • z) = a • σ z := fun a z => map_smul σ₀ a z
  have hs : ∀ a, ∃ z b, a = σ z + (p ^ n) • b :=
    surj_mod_pow σ.toAddMonoidHom p (fun a => by
      obtain ⟨z, b, h⟩ := hu.span a
      exact ⟨z, b, h.trans (by rw [← hσ]; rfl)⟩) n
  have hrk : Module.finrank ℤ La = Module.finrank ℤ (Fin N → 𝓞 E) := by
    rw [hu.rank, Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  let φ := LinearEquiv.ofFinrankEq La (Fin N → 𝓞 E) hrk
  have hk : ∀ z b, σ z = (p ^ n) • b → ∃ z', z = (p ^ n) • z' := fun z b h =>
    inj_mod_of_surj_mod (φ.toLinearMap ∘ₗ σ) (p ^ n) (fun a => by
      obtain ⟨z, b, h⟩ := hs (φ.symm a)
      refine ⟨z, φ b, ?_⟩
      have := congrArg φ h
      rwa [φ.apply_symm_apply, map_add, map_nsmul] at this) z (φ b) (by
      show φ (σ z) = _
      rw [h, map_nsmul])
  obtain ⟨hsu, hin⟩ := perfect_mod σ (p ^ n) EF hu.unimod hs hk
  let K : Submodule ℤ La := LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))
  let π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n :=
    AddMonoidHom.toMultiplicative (K.mkQ ∘ₗ σ).toAddMonoidHom
  have hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p n (σ z) := fun z => rfl
  let e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n) :=
    { toFun := fun y => (Int.castAddHom (ZMod (p ^ n))).comp (EF (σ y) ∘ₗ σ).toAddMonoidHom
      map_zero' := by ext z; simp
      map_add' := fun y y' => by ext z; simp }
  have he : ∀ y z, e y z = ((EF (σ y) (σ z) : ℤ) : ZMod (p ^ n)) := fun y z => rfl
  have hone : ∀ a : La, lev p n a = 1 ↔ ∃ b, a = (p ^ n) • b := fun a => by
    show (Submodule.Quotient.mk a : La ⧸ K) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  refine ⟨π, e, fun z => by rw [hπ, hσ], fun z z' => by rw [he, hσ, hσ], fun a => ?_, fun t => ?_, fun y => ?_,
    fun y => ?_, fun a y z => ?_, fun ψ => ?_, fun y hy => ?_⟩
  · simpa only [hσ] using hs a
  · obtain ⟨a, ha⟩ := K.mkQ_surjective (Multiplicative.toAdd t)
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    have h0 : K.mkQ ((p ^ n) • b) = 0 := (hone _).2 ⟨b, rfl⟩
    rw [map_add, h0, add_zero] at ha
    exact ha
  · rw [hπ, hone]
    exact ⟨fun ⟨b, hb⟩ => hk y b hb, fun ⟨y', hy'⟩ => ⟨σ y', by rw [hy', map_nsmul]⟩⟩
  · rw [he, hu.alt, Int.cast_zero]
  · rw [he, he, hσa, hσa, hu.adj]
  · obtain ⟨y, hy⟩ := hsu ψ
    exact ⟨y, AddMonoidHom.ext hy⟩
  · exact hin y fun z => (he y z).symm.trans (by rw [hy]; rfl)

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.Invres
section
noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

open ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

lemma unimod {S V ι : Type} [CommRing S] [CommRing V] [Algebra S V] [Fintype ι] (f : ι → V)
    (b : ι → S) (h1 : 1 = ∑ j, b j • f j)
    (hmul : ∀ i j, f j * f i ∈ Submodule.span S (Set.range f)) :
    ∃ e : ι → S, algebraMap S V (∑ j, e j * b j) = 1 := by
  let A : Submodule S V := Submodule.span S (Set.range f)
  let J : Ideal S := Ideal.span (Set.range b)
  have hJ : A ≤ J • A := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : f i = ∑ j, b j • (f j * f i) := by
      conv_lhs => rw [← one_mul (f i), h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
    rw [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul
      (Ideal.subset_span ⟨j, rfl⟩) (hmul i j)
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J A
    (Submodule.fg_span (Set.finite_range f)) hJ
  have h1A : (1 : V) ∈ A := by
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => A.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hr := hr0 1 h1A
  rw [Algebra.smul_def, mul_one] at hr
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 (J.neg_mem hr1)
  refine ⟨e, ?_⟩
  simp only [smul_eq_mul] at he
  rw [he, neg_sub, map_sub, hr, map_one, sub_zero]

theorem invres : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ K K' : AddSubgroup N, K ≤ K' → ∀ g ∈ AA.carrier, (∀ x ∈ K', ∀ k ∈ K, g (x + k) = g x) → ∃ g' ∈ invFun AA.carrier K, ∀ x ∈ K', g' x = g x := by
  intro p _ C _ _ _ v R _ _ hv _ N _ _ _ AA K K' _ g hg hinv
  classical
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  obtain ⟨⟨f, hf, hfree⟩, -⟩ := ReciprocityTheory.PGsh.L2.h3 C R inferInstance inferInstance v hv N K AA
  have hB : ∀ b ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K), b ∈ invFun AA.carrier K := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hq, fun x k hk => ?_⟩
    show q ((x + k : N) : N ⧸ K) = q (x : N ⧸ K)
    rw [QuotientAddGroup.mk_add_of_mem x hk]
  have hdec : ∀ a ∈ AA.carrier, ∃ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) ∧
      a = ∑ j, b j * f j := by
    intro a ha
    obtain ⟨b, ⟨hb, hab⟩, -⟩ := hfree a ha
    exact ⟨b, fun j => hB _ (hb j), hab⟩
  let S : Subalgebra R (N → C) := (invFun AA.carrier K).toSubalgebra ⟨AA.one_mem, fun _ _ _ => rfl⟩
    (fun x y hx hy => ⟨AA.mul_mem _ _ hx.1 hy.1, fun z k hk => by
      simp only [Pi.mul_apply, hx.2 z k hk, hy.2 z k hk]⟩)
  let A : Submodule S (N → C) := Submodule.span S (Set.range f)
  have hA : ∀ a ∈ AA.carrier, a ∈ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := hdec a ha
    exact Submodule.sum_mem _ fun j _ =>
      A.smul_mem (⟨b j, hb j⟩ : S) (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hb, h1⟩ := hdec 1 AA.one_mem
  obtain ⟨e, he⟩ := unimod f (fun j => (⟨b j, hb j⟩ : S)) h1
    (fun i j => hA _ (AA.mul_mem _ _ (hf j) (hf i)))
  have he' : ∀ x, ∑ j, (e j : N → C) x * b j x = 1 := by
    intro x
    have : ((∑ j, e j * (⟨b j, hb j⟩ : S) : S) : N → C) x = 1 := congrFun he x
    simpa using this
  obtain ⟨c, hc, hgc⟩ := hdec g hg
  refine ⟨((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C), (∑ j, e j * (⟨c j, hc j⟩ : S) : S).2,
    fun x hx => ?_⟩
  let ρ : (N → C) →ₗ[C] (K → C) := LinearMap.funLeft C C fun k : K => x + (k : N)
  have hρ : ∀ b : K → N → C, (∀ j, b j ∈ invFun AA.carrier K) →
      ρ (∑ j, b j * f j) = ∑ j, b j x • ρ (f j) := by
    intro b hb
    funext k
    simp only [ρ, LinearMap.funLeft_apply, Finset.sum_apply, Pi.mul_apply, Pi.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [(hb j).2 x k k.2]
  have hli : LinearIndependent C fun j => ρ (f j) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · have hsurj : Function.Surjective ρ :=
        LinearMap.funLeft_surjective_of_injective _ _ _
          (fun k k' h => Subtype.ext (add_left_cancel h))
      rw [← LinearMap.range_eq_top.2 hsurj, ← Submodule.map_top, ← span_top_of_isLat (C := C) AA.lat,
        Submodule.map_span_le]
      intro a ha
      obtain ⟨b', hb', rfl⟩ := hdec a ha
      rw [hρ b' hb']
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp
  have hkey : ∀ j, c j x = g x * b j x := by
    have h2 : ∑ j, (c j x - g x * b j x) • ρ (f j) = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [← hρ c hc, ← hρ b hb, ← hgc, ← h1]
      funext k
      simp [ρ, LinearMap.funLeft_apply, hinv x hx k k.2]
    intro j
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 j)
  have : ((∑ j, e j * (⟨c j, hc j⟩ : S) : S) : N → C) x = ∑ j, (e j : N → C) x * c j x := by
    simp
  rw [this]
  simp only [hkey]
  calc ∑ j, (e j : N → C) x * (g x * b j x) = g x * ∑ j, (e j : N → C) x * b j x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    _ = g x := by rw [he', mul_one]

end PositivityTheory.HtPt.Rc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPullEq
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LPullEq

theorem pull_eq_pullLoc_of_dominates : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type)
    [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F]
    (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i →
      L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' := by
  intro o _ Ω _ _ κ _ x M E _ _ L X' Ω' _ ξ' i F _ _ j f hL hd
  have dl := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ X' Ω' ξ' i f hd
  refine ⟨?_, fun p' => ?_⟩
  · funext p'
    obtain ⟨h, hc⟩ := dl p'
    rw [PositivityTheory.HtPt.Mb.pullloc_centre o Ω κ x M E L X' Ω' ξ' i F j ⟨f p'.1, h⟩ p' hL hc]
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨h, e, he, rfl⟩
  · obtain ⟨h, h1, -⟩ := dl p'
    obtain ⟨c, hc⟩ := M.tie.cover ⟨f p'.1, h⟩
    exact ⟨c, hc.1, fun a ha => h1 a (((M.tie.ring c hc.1) a).1 ha _ hc)⟩

end PositivityTheory.HtPt.Mb.LPullEq

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.pull_eq : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (f : X' ⟶ M.X), L.IsCohOn Set.univ → Dominates ξ' M.ξ f i → L.pull ξ' f j = L.pullLoc ξ' i j ∧ ∀ p', p' ∈ ctrSet o x i ξ' :=
  @PositivityTheory.HtPt.Mb.LPullEq.pull_eq_pullLoc_of_dominates
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MhQuot
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

theorem quot : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (H : Type) [CommGroup H] [Finite H] (Γ₁ : QFGroup R H) (a : Γ₁.G ⟶ Γ.G) [IsMonHom a] (α : H →* T), (∀ h, Γ₁.pt h ≫ a = Γ.pt (α h)) → IsFinite Γ₁.G.hom → IsFinite Γ.G.hom → Flat a.left → Surjective a.left → quotOrder α (Γ₁.btOrder ⊤) = Γ.btOrder ⊤ := by
  intro R _ _ _ T _ _ Γ H _ _ Γ₁ a _ α hpt hfin₁ hfin hfl hsurj
  haveI : IsAffine Γ.G.left := isAffine_of_isAffineHom Γ.G.hom
  haveI : IsAffine Γ₁.G.left := isAffine_of_isAffineHom Γ₁.G.hom
  have hα : Function.Surjective α := by
    intro t
    let z : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
    obtain ⟨y, hy⟩ := a.left.surjective ((Γ.pt t).left z)
    have hgen : (Γ₁.G.hom y).asIdeal = ⊥ := by
      have e1 : Γ₁.G.hom y = Γ.G.hom ((Γ.pt t).left z) := by
        rw [← hy, ← Scheme.Hom.comp_apply, Over.w a]
      rw [e1, ← Scheme.Hom.comp_apply, Over.w (Γ.pt t)]
      show (PrimeSpectrum.comap (algebraMap R (FractionRing R)) z).asIdeal = ⊥
      rw [PrimeSpectrum.comap_asIdeal]
      have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.isPrime.ne_top
      rw [hz]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
    obtain ⟨h, x, hx⟩ := Γ₁.pt_onto y hgen
    refine ⟨h, Γ.pt_inj (α h) t x z ?_⟩
    have e2 : a.left ((Γ₁.pt h).left x) = (Γ.pt (α h)).left x := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hpt h]
    rw [← e2, hx, hy]
  ext f
  rw [quotOrder, Subalgebra.mem_comap, mem_top_iff, mem_top_iff]
  constructor
  · intro hf t
    obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_denominator_btOrder R T Γ
    obtain ⟨s0, hs0⟩ := (mem_top_iff Γ _).1 (hd (fun x => f (t * x))) 1
    obtain ⟨h0, rfl⟩ := hα t
    obtain ⟨s₁, hs₁⟩ := hf h0
    have key : a.left.appTop s0 = a.left.appTop (pb Γ.G.hom d) * s₁ := by
      apply sec_ext Γ₁
      intro h
      rw [map_mul, ← val_comp, ← val_comp, ← Over.comp_left, hpt h, hs0, val_const, hs₁, ← map_mul]
      congr 1
      show d * f (α h0 * (1 * α h)) = d * f (α (h0 * h))
      rw [_root_.one_mul, MonoidHom.map_mul]
    have e : Spec.map a.left.appTop = Γ₁.G.left.isoSpec.inv ≫ a.left ≫ Γ.G.left.isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    have hff : a.left.appTop.hom.FaithfullyFlat :=
      (flat_and_surjective_SpecMap_iff _).1 ⟨by rw [e]; infer_instance, by rw [e]; infer_instance⟩
    letI : Algebra Γ(Γ.G.left, ⊤) Γ(Γ₁.G.left, ⊤) := a.left.appTop.hom.toAlgebra
    have hmem : s0 ∈ Ideal.span {pb Γ.G.hom d} := by
      rw [← @Ideal.comap_map_eq_self_of_faithfullyFlat _ _ _ _ _ hff (Ideal.span {pb Γ.G.hom d}),
        Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact ⟨s₁, key⟩
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨s, fun h => ?_⟩
    have e3 := hs0 h
    rw [← hs, map_mul, val_const] at e3
    have hd' : algebraMap R (FractionRing R) d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hd0
    apply mul_right_cancel₀ hd'
    rw [e3, ← map_mul]
    congr 1
    show d * f (α h0 * (1 * h)) = f (α h0 * h) * d
    rw [_root_.one_mul, mul_comm]
  · intro hf h0
    obtain ⟨s, hs⟩ := hf (α h0)
    refine ⟨a.left.appTop s, fun h => ?_⟩
    rw [← val_comp, ← Over.comp_left, hpt h, hs]
    exact congrArg _ (congrArg f (map_mul α h0 h).symm)

end PositivityTheory.HtPt.Mh
end
end

