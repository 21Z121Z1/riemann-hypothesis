import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0016
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0017
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpB
section
noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace PositivityTheory.HtPt.Farsharp

theorem mem_of_forall_dvd {O A : Type} [CommRing O] [IsDomain O] [ValuationRing O] [AddCommGroup A]
    [Module O A] [Module.IsTorsionFree O A] (N : Submodule O A) (hN : N.FG) {q : O} (hq : q ≠ 0)
    (hqN : ∀ a, q • a ∈ N) (x : A)
    (h : ∀ φ : A →ₗ[O] O, (∀ y ∈ N, q ∣ φ y) → q ∣ φ x) : x ∈ N := by
  classical
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  haveI : Module.Flat O N := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  haveI : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O N
  let ψ : A →ₗ[O] N := LinearMap.codRestrict N (q • LinearMap.id) (fun a => hqN a)
  have hψ : ∀ a, (ψ a : A) = q • a := fun a => rfl
  have key : ∀ i, q ∣ b.coord i (ψ x) := by
    intro i
    apply h ((b.coord i).comp ψ)
    intro y hy
    have hy' : ψ y = q • (⟨y, hy⟩ : N) := Subtype.ext (hψ y)
    rw [LinearMap.comp_apply, hy', map_smul, smul_eq_mul]
    exact dvd_mul_right _ _
  choose d hd using key
  let z : N := ∑ i, d i • b i
  have hz : ψ x = q • z := by
    apply b.ext_elem
    intro i
    have := hd i
    simp only [Module.Basis.coord_apply] at this
    simp [z, this, Finset.smul_sum, smul_smul, Finsupp.single_apply]
  have hxz : x = (z : A) := by
    have h1 : q • x = q • (z : A) := by
      rw [← hψ, hz]; rfl
    exact Module.IsTorsionFree.isSMulRegular (isRegular_of_ne_zero hq) h1
  rw [hxz]
  exact z.2

variable {p : ℕ} {O : Type} [CommRing O]

theorem dUnit_mulBy {A : Type} [CommRing A] [Bialgebra O A] [IsCocomm O A] (k : ℕ) (a : A) :
    dUnit O (mulBy O A k a) = (k : O) • dUnit O a := by
  rw [← cotMap_d]
  show cotMap ((toConv (BialgHom.id O A) ^ k).ofConv) (dUnit O a) = _
  rw [cotMap_pow, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  simp [cotMap_id]

theorem dUnit_of_mem_torsionIdeal {A : Type} [CommRing A] [Bialgebra O A] [IsCocomm O A] (k : ℕ)
    {t : A} (ht : t ∈ torsionIdeal O A k) : ∃ y, dUnit O t = (k : O) • y := by
  suffices H : counitAlgHom O A t = 0 ∧ ∃ y, dUnit O t = (k : O) • y from H.2
  change t ∈ Ideal.span _ at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨?_, dUnit O a, dUnit_mulBy k a⟩
    have ha' : counitAlgHom O A a = 0 := ha
    simpa using ha'
  | zero => exact ⟨by simp, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx0, u, hu⟩ := hx
    obtain ⟨hy0, v, hv⟩ := hy
    exact ⟨by rw [map_add, hx0, hy0, add_zero], u + v, by simp [hu, hv, smul_add]⟩
  | smul c x _ hx =>
    obtain ⟨hx0, u, hu⟩ := hx
    refine ⟨by rw [smul_eq_mul, map_mul, hx0, mul_zero], counitAlgHom O A c • u, ?_⟩
    show AugCot.d _ (c * x) = _
    rw [AugCot.d_mul, hx0, zero_smul, add_zero]
    change _ • dUnit O x = _
    rw [hu, smul_comm]

theorem exists_of_cotMap_res_eq_zero (G : PDivGroup p O) (n : ℕ) (y : Cot O (G.A (n + 1)))
    (hy : cotMap (G.res n) y = 0) : ∃ y', y = (p : O) ^ n • y' := by
  unfold cotMap at hy
  obtain ⟨x, hx⟩ := (AugCot.exact_kerMap_map _ _ (G.res_surjective n) y).1 hy
  have hx' : dUnit O (x : G.A (n + 1)) = y := by
    rw [← hx]
    exact (AugCot.kerMap_apply _ _ x).symm
  have hxmem : (x : G.A (n + 1)) ∈ torsionIdeal O (G.A (n + 1)) (p ^ n) := by
    rw [← G.ker_res n]
    exact x.2
  obtain ⟨y', hy'⟩ := dUnit_of_mem_torsionIdeal (p ^ n) hxmem
  refine ⟨y', ?_⟩
  rw [← hx', ← Nat.cast_pow]
  exact hy'

def lev (G : PDivGroup p O) (n : ℕ) : G.omega →ₗ[O] Cot O (G.A n) :=
  LinearMap.proj n ∘ₗ G.omegaSub.subtype

theorem lev_apply (G : PDivGroup p O) (n : ℕ) (w : G.omega) : lev G n w = w.1 n := rfl

private theorem prime_pow_smul_cot_eq_zero (G : PDivGroup p O) (n : ℕ) (y : Cot O (G.A n)) :
    (p : O) ^ n • y = 0 := by
  obtain ⟨b, rfl⟩ := AugCot.d_surjective _ y
  obtain ⟨a, rfl⟩ := G.res_surjective n b
  set r := counitAlgHom O (G.A (n + 1)) a
  have hmem : mulBy O (G.A (n + 1)) (p ^ n) (a - algebraMap O _ r) ∈ RingHom.ker (G.res n) := by
    rw [G.ker_res n]
    apply Ideal.mem_map_of_mem
    show a - algebraMap O _ r ∈ RingHom.ker (counitAlgHom O (G.A (n + 1)))
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp [r]
  have h2 : G.res n (mulBy O _ (p ^ n) a) = algebraMap O _ r := by
    rw [RingHom.mem_ker] at hmem
    have := hmem
    simp only [map_sub, AlgHomClass.commutes, sub_eq_zero] at this
    exact this
  rw [← Nat.cast_pow]
  change ((p ^ n : ℕ) : O) • dUnit O (G.res n a) = 0
  rw [← dUnit_mulBy, ← map_mulBy, h2]
  exact AugCot.d_algebraMap _ _

theorem smul_mem_of_levels [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O)
    (L : Submodule O G.omega) (hL : L.FG) (κ : O)
    (hκ : ∀ n (y : Cot O (G.A n)), κ • y ∈ L.map (lev G n))
    (hp : ∀ n (y : Cot O (G.A n)), (p : O) • y ∈ L.map (lev G n)) (w : G.omega) : κ • w ∈ L := by
  classical
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let g : (Fin m → O) →ₗ[O] G.omega := Fintype.linearCombination O s
  have hg : LinearMap.range g = L := by rw [Fintype.range_linearCombination, hs]
  let Φ : (k : ℕ) → (Fin m → O) →ₗ[O] Cot O (G.A k) := fun k => (lev G k).comp g
  have compat : ∀ k (v : G.omega), cotMap (G.res k) (lev G (k + 1) v) = lev G k v := by
    intro k v
    rw [lev_apply, lev_apply]
    exact v.2 k
  have compatΦ : ∀ k c, cotMap (G.res k) (Φ (k + 1) c) = Φ k c := fun k c => compat k (g c)
  have lift : ∀ k (y : Cot O (G.A k)), y ∈ L.map (lev G k) → ∃ c, Φ k c = y := by
    intro k y hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
    rw [← hg] at hv
    obtain ⟨c, rfl⟩ := hv
    exact ⟨c, rfl⟩
  let W : (k : ℕ) → Cot O (G.A k) := fun k => lev G k w
  have hWc : ∀ k, cotMap (G.res k) (κ • W (k + 1)) = κ • W k := by
    intro k
    rw [map_smul, compat]
  have step : ∀ n (c : {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)}),
      ∃ c' : {c : Fin m → O // Φ (n + 2) c = κ • W (n + 2)},
        ∃ f : Fin m → O, c'.1 = c.1 + (p : O) ^ n • f := by
    intro n c
    obtain ⟨d, hd⟩ := lift (n + 2) _ (hκ (n + 2) (W (n + 2)))
    have hd1 : Φ (n + 1) d = κ • W (n + 1) := by
      rw [← compatΦ, hd, hWc]
    have he : cotMap (G.res (n + 1)) (Φ (n + 2) (d - c.1)) = 0 := by
      rw [compatΦ, map_sub, hd1, c.2, sub_self]
    obtain ⟨y', hy'⟩ := exists_of_cotMap_res_eq_zero G (n + 1) _ he
    obtain ⟨f, hf⟩ := lift (n + 2) _ (hp (n + 2) y')
    refine ⟨⟨c.1 + (p : O) ^ n • f, ?_⟩, f, rfl⟩
    have key : Φ (n + 2) (d - c.1) = Φ (n + 2) ((p : O) ^ n • f) := by
      rw [hy', map_smul, hf, smul_smul, ← pow_succ]
    have : c.1 + (p : O) ^ n • f = d - (d - c.1) + (p : O) ^ n • f := by abel
    rw [this, map_add, map_sub, key, hd]
    abel
  choose nxt hnxt using step
  obtain ⟨c0, hc0⟩ := lift 1 _ (hκ 1 (W 1))
  let seq : (n : ℕ) → {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)} :=
    fun n => @Nat.rec (fun n => {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)}) ⟨c0, hc0⟩
      (fun k ck => nxt k ck) n
  have seq_succ : ∀ n, seq (n + 1) = nxt n (seq n) := fun n => rfl
  have diff : ∀ a b, a ≤ b → ∃ t : Fin m → O, (seq b).1 = (seq a).1 + (p : O) ^ a • t := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ b hab ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨f, hf⟩ := hnxt b (seq b)
      refine ⟨t + (p : O) ^ (b - a) • f, ?_⟩
      rw [seq_succ, hf, ht, smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hab, add_assoc]
  have hpre : ∀ j, ∃ l : O, ∀ n, (seq n).1 j ≡ l [SMOD ((Ideal.span {(p : O)}) ^ n • ⊤ : Submodule O O)] := by
    intro j
    apply IsPrecomplete.prec inferInstance
    intro a b hab
    obtain ⟨t, ht⟩ := diff a b hab
    rw [SModEq.sub_mem, ht]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_add_cancel_left, Ideal.mul_top]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) a))
  choose l hl using hpre
  have close : ∀ N, ∃ t : Fin m → O, l = (seq N).1 + (p : O) ^ N • t := by
    intro N
    have : ∀ j, ∃ a : O, a * (p : O) ^ N = l j - (seq N).1 j := by
      intro j
      have h1 := (SModEq.sub_mem.1 (hl j N).symm)
      simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h1
      exact Ideal.mem_span_singleton'.1 h1
    choose t ht using this
    refine ⟨t, funext fun j => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ht]
    ring
  have good : ∀ n, Φ (n + 1) l = κ • W (n + 1) := by
    intro n
    obtain ⟨t, ht⟩ := close (n + 1)
    have h1 : Φ (n + 1) (seq (n + 1)).1 = κ • W (n + 1) := by
      rw [← compatΦ, (seq (n + 1)).2, hWc]
    rw [ht, map_add, h1, map_smul, prime_pow_smul_cot_eq_zero, add_zero]
  have good' : ∀ n, Φ n l = κ • W n := by
    intro n
    cases n with
    | zero => rw [← compatΦ, good 0, hWc]
    | succ n => exact good n
  have hgl : g l = κ • w := by
    apply Subtype.ext
    funext k
    have := good' k
    simp only [Φ, W, LinearMap.comp_apply, lev_apply] at this
    rw [this]
    rfl
  rw [← hg, ← hgl]
  exact LinearMap.mem_range_self g l

end PositivityTheory.HtPt.Farsharp
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GcChart
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem om'_le : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem pow_smul_mem {x : Ω} (hx : x ∈ D.om) : ((p : A) ^ R) • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem ht_mem_span {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ' : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    (φ : A →+* O) (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[φ] Ω') (hred : D.ReducesTo φ P ι)
    {t : V} (ht : t ∈ P.T) :
    P.ht t ∈ Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) := by
  classical
  set S := Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'})
  have hp : ∀ y ∈ P.om, (p ^ R) • y ∈ S := by
    intro y hy
    rw [← hred.span_eq] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, rfl⟩ := hw
      refine Submodule.subset_span ⟨(p ^ R) • m, ?_, map_nsmul ι _ _⟩
      have := pow_smul_mem D m.2
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
      exact this
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact S.add_mem ha hb
    | smul a w _ hw => rw [smul_comm]; exact S.smul_mem a hw
  have hT : P.T ≤ S.comap (P.ht.restrictScalars O) := by
    rw [P.free.2.2, Submodule.span_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := hred.ht_eq (Pi.single i (RingOfIntegers.basis E k))
    have h1 : P.tate (Pi.single i (RingOfIntegers.basis E k)) =
        P.ρ (RingOfIntegers.basis E k) (P.t i) := by
      rw [HTPoint.tate, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [h1] at he
    change P.ht (P.ρ (RingOfIntegers.basis E k) (P.t i)) ∈ S
    rw [← sub_eq_iff_eq_add.2 he]
    exact S.sub_mem (Submodule.subset_span ⟨_, h_mem_om' D _, rfl⟩) (hp y hy)
  exact hT ht

end

theorem chart_ii : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A), κ ∣ (p : A) ^ R → Module.Projective A D.om' → D.HasTestPoints κ → D.om' ≤ D.om ∧ (∀ x ∈ D.om, κ • x ∈ D.om') := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N hp Ω _ _ _ _ D κ hκ hP hT
  refine ⟨om'_le D, fun x hx => ?_⟩
  have hp0 : algebraMap A K ((p : A) ^ R) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hlat : D.om'.IsLattice K := by
    haveI : Module.Finite A D.om := haveI := D.om_lat; Submodule.IsLattice.finite K D.om
    refine ⟨Submodule.FG.of_le D.om_lat.fg (om'_le D), ?_⟩
    rw [eq_top_iff, ← D.om_lat.span_eq_top, Submodule.span_le]
    intro y hy
    have : y = (algebraMap A K ((p : A) ^ R))⁻¹ • (((p : A) ^ R) • y) := by
      rw [← algebraMap_smul K ((p : A) ^ R) y, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (pow_smul_mem D hy))
  refine test_incl A K Ω D.om' _ hlat hP fun q hq h1 => ?_
  by_cases hpq : (p : A) ∈ q
  swap
  · refine ⟨(p : A) ^ R, fun h => hpq (hq.mem_of_pow_mem R h), ?_⟩
    exact pow_smul_mem D (D.om.smul_mem κ hx)
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, hcen, hred⟩ :=
    hT q hq h1 hpq
  letI : Algebra A O := φ.toAlgebra
  obtain ⟨j, hj, -, hj1⟩ := bc_iso A K Ω D.om C v O hv Ω' P.om ι D.om_lat D.om_proj P.om_lat
    hred.span_eq hred.rank_eq
  obtain ⟨s, hs, hsx⟩ := test_descend A K C v O hv q D.om (D.om'.comap D.om.subtype)
    (κ • ⟨x, hx⟩) hq h1 hφ hcen (by
      obtain ⟨t, ht, hte⟩ := P.κ_mem (ι ⟨x, hx⟩)
        (hred.span_eq ▸ Submodule.subset_span ⟨_, rfl⟩)
      have h2 := ht_mem_span D φ P ι hred ht
      rw [hte, ← ι.map_smulₛₗ, ← hj1] at h2
      have h3 : Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) =
          (Submodule.span O ((fun y : D.om => (1 : O) ⊗ₜ[A] y) ''
            (D.om'.comap D.om.subtype : Set D.om))).map j := by
        rw [Submodule.map_span, Set.image_image]
        simp only [hj1]
        rfl
      rw [h3] at h2
      obtain ⟨z, hz, hze⟩ := h2
      rwa [← hj hze])
  exact ⟨s, hs, hsx⟩

end PositivityTheory.HtPt.Gc
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentreUnique
section
noncomputable section

namespace PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  show IsLocalRing (genMap ξ p).range
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have e : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have ha : (a : Ω) ≠ 0 := fun h0 => by simp [h0] at e
    refine ⟨ha, a.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right e]
    exact b.2
  · rintro ⟨h0, -, h2⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem unitAt_iff_of_dominated {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'} {q : Cpt ξ}
    (h : (∀ a ∈ regAt ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ q, unitAt ξ' p' (i a) → unitAt ξ q a)
    {a : Ω} (ha : a ∈ regAt ξ q) : unitAt ξ q a ↔ unitAt ξ' p' (i a) := by
  refine ⟨fun hu => ⟨(map_ne_zero i).2 hu.1, h.1 a hu.2.1, ?_⟩, h.2 a ha⟩
  rw [← map_inv₀]
  exact h.1 _ hu.2.2

theorem eq_of_dominated_of_inChart {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {i : Ω →+* Ω'} {p' : Cpt ξ'} {c : κ} {q r : Cpt M.ξ} (hq : InChart M.ξ x c q) (hr : InChart M.ξ x c r)
    (dq : (∀ a ∈ regAt M.ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q, unitAt ξ' p' (i a) → unitAt M.ξ q a)
    (dr : (∀ a ∈ regAt M.ξ r, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ r, unitAt ξ' p' (i a) → unitAt M.ξ r a) :
    q = r := by
  have cq := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c q hq).1
  have cr := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c r hr).1
  haveI := isLocalRing_regAt M.ξ q
  let f : chRing o x c →+* regAt M.ξ q :=
    ((chRing o x c).val : chRing o x c →+* Ω).codRestrict (regAt M.ξ q) fun u => cq _ u.2
  have hP : ∀ u : chRing o x c, u ∈ (IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f ↔ ¬ unitAt M.ξ q (u : Ω) := by
    intro u
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
    rfl
  obtain ⟨p, -, huniq⟩ := PositivityTheory.HtPt.Ma.prime_pt o Ω κ x M c hq.1 _
    (inferInstance : ((IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f).IsPrime)
  have e1 := huniq q ⟨hq, hP⟩
  have e2 := huniq r ⟨hr, fun u => by
    rw [hP, unitAt_iff_of_dominated dq (cq _ u.2), unitAt_iff_of_dominated dr (cr _ u.2)]⟩
  exact e1.trans e2.symm

theorem eq_of_dominated : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' q₁ q₂ d₁ d₂
  obtain ⟨c₁, hc₁⟩ := M.tie.cover q₁
  obtain ⟨c₂, hc₂⟩ := M.tie.cover q₂
  have hctr : p' ∈ ctrSet o x i ξ' :=
    ⟨c₁, hc₁.1, fun a ha => d₁.1 a ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c₁ q₁ hc₁).1 a ha)⟩
  obtain ⟨p₀, d₀, -, hp₀⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M X' Ω' ξ' i p' hctr
  have e₁ : q₁ = p₀ := eq_of_dominated_of_inChart M hc₁ (hp₀ c₁ hc₁.1 fun j => d₁.1 _ (hc₁.2 j)) d₁ d₀
  have e₂ : q₂ = p₀ := eq_of_dominated_of_inChart M hc₂ (hp₀ c₂ hc₂.1 fun j => d₂.1 _ (hc₂.2 j)) d₂ d₀
  exact e₁.trans e₂.symm

end PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.centre_unique : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ :=
  @PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep.eq_of_dominated
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPulllocCentre
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LPulllocCentre

theorem pullLoc_eq_span_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (p₀ : Cpt M.ξ) (p' : Cpt ξ'), L.IsCohOn Set.univ → ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) → L.pullLoc ξ' i j p' = Submodule.span (regAt ξ' p') (j '' (L p₀ : Set E)) := by
  intro o _ Ω _ _ κ _ x M E _ _ L X' Ω' _ ξ' i F _ _ j p₀ p' hcoh hdom
  obtain ⟨hd1, hd2⟩ := hdom
  obtain ⟨c, hc⟩ := M.tie.cover p₀
  have hcx : x c ≠ 0 := hc.1
  have hch0 : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p₀ := fun a ha => (M.tie.ring c hcx a).1 ha p₀ hc
  have hctr : p' ∈ ctrSet o x i ξ' := ⟨c, hcx, fun a ha => hd1 a (hch0 a ha)⟩
  obtain ⟨p₁, ⟨h11, -⟩, h13, h14⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M X' Ω' ξ' i p' hctr
  have hp1c : InChart M.ξ x c p₁ := h14 c hcx fun k => hd1 _ (hc.2 k)
  have hle : regAt M.ξ p₁ ≤ regAt M.ξ p₀ := by
    intro a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p₁ hp1c).2 a).1 ha
    have hiv : unitAt ξ' p' (i v) :=
      ⟨(map_ne_zero i).2 hvu.1, h11 _ hvu.2.1, by rw [← map_inv₀]; exact h11 _ hvu.2.2⟩
    have hv0 : unitAt M.ξ p₀ v := hd2 v (hch0 v hv) hiv
    rw [div_eq_mul_inv]
    exact mul_mem (hch0 u hu) hv0.2.2
  have hsp : p₀.1 ⤳ p₁.1 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p₁ p₀).1 hle
  have hstalk : ∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → ∀ e ∈ L p, e ∈ L p₀ := by
    intro p hp e he
    have hs : p₀.1 ⤳ p.1 := hsp.trans (h13 p hp)
    obtain ⟨U, hU, n, b, hb⟩ := hcoh p (Set.mem_univ p)
    have h0U : p₀.1 ∈ U := hs.mem_open U.isOpen hU
    have hreg : regAt M.ξ p ≤ regAt M.ξ p₀ := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p p₀).2 hs
    rw [hb p (Set.mem_univ p) hU] at he
    rw [hb p₀ (Set.mem_univ p₀) h0U]
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy => exact Submodule.smul_mem _ (⟨a, hreg a.2⟩ : regAt M.ξ p₀) hy
  exact Lat.pullLoc_eq_span_of_ctr j ⟨hd1, hd2⟩ fun p hp => hstalk p hp.1

end PositivityTheory.HtPt.Mb.LPulllocCentre

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.pullloc_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (F : Type) [AddCommGroup F] [Module Ω' F] (j : E →+ F) (p₀ : Cpt M.ξ) (p' : Cpt ξ'), L.IsCohOn Set.univ → ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) → L.pullLoc ξ' i j p' = Submodule.span (regAt ξ' p') (j '' (L p₀ : Set E)) :=
  @PositivityTheory.HtPt.Mb.LPulllocCentre.pullLoc_eq_span_centre
end

