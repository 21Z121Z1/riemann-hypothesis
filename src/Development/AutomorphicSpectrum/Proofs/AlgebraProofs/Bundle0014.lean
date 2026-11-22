import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0003
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
section
noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegFrob

variable {K : Type} [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]

theorem det_frobVec {d : ℕ} (b : Fin d → Fin d → K) :
    (Pi.basisFun K (Fin d)).det (fun q => frobVec p (b q)) =
      ((Pi.basisFun K (Fin d)).det b) ^ p := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  rw [Module.Basis.det_apply, Module.Basis.det_apply, ← frobenius_def, RingHom.map_det]
  congr 1

theorem exists_frob_basis {n d : ℕ} (b : Module.Basis (Fin n) K (Fin d → K)) :
    ∃ b' : Module.Basis (Fin n) K (Fin d → K), ∀ q, b' q = frobVec p (b q) := by
  have hnd : n = d := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_fin] at h
    exact h.symm
  subst hnd
  have hb : IsUnit ((Pi.basisFun K (Fin n)).det b) :=
    (Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).1 ⟨b.linearIndependent, b.span_eq⟩
  have hb' : IsUnit ((Pi.basisFun K (Fin n)).det (fun q => frobVec p (b q))) := by
    rw [det_frobVec p (⇑b)]; exact hb.pow p
  obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).2 hb'
  exact ⟨Module.Basis.mk hli hsp.ge, fun q => Module.Basis.mk_apply _ _ _⟩

theorem repr_frobVec {n d : ℕ} (b b' : Module.Basis (Fin n) K (Fin d → K))
    (h : ∀ q, b' q = frobVec p (b q)) (y : Fin d → K) (q : Fin n) :
    b'.repr (frobVec p y) q = (b.repr y q) ^ p := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  have key : frobVec p y = ∑ i, (b.repr y i) ^ p • b' i := by
    conv_lhs => rw [← b.sum_repr y]
    funext j
    simp only [frobVec, h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_pow_char, mul_pow]
  rw [key, Module.Basis.repr_sum_self]

theorem isLatOf_frob {n d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) (i : C.I)
    (b b' : Module.Basis (Fin n) K (Fin d → K))
    (h : ∀ q, b' q = frobVec p (b q)) (hb : IsLatOf C i b (L i)) :
    IsLatOf C i b' (frobLat C p L i) := by
  intro x
  change x ∈ AddSubgroup.closure _ ↔ _
  constructor
  · intro hx
    have hle : AddSubgroup.closure {y | ∃ (a : K) (z : Fin d → K), C.v i a ≤ 1 ∧ z ∈ L i ∧
        y = a • frobVec p z} ≤ GlobalTheory.CompanionTheory.Ar.Crv.Inhab.latOf C i b' := by
      rw [AddSubgroup.closure_le]
      rintro y ⟨a, z, ha, hz, rfl⟩
      change ∀ q, C.v i (b'.repr (a • frobVec p z) q) ≤ 1
      intro q
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, repr_frobVec p b b' h z q, map_mul, map_pow]
      exact mul_le_one' ha (pow_le_one' ((hb z).1 hz q) p)
    exact hle hx
  · intro hx
    rw [← b'.sum_repr x]
    refine AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure
      ⟨b'.repr x q, b q, hx q, (hb (b q)).2 fun r => ?_, by rw [h]⟩
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem isBun_frobLat {d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) (hL : IsBun C L) :
    IsBun C (frobLat C p L) := by
  obtain ⟨h1, b₀, hfin⟩ := hL
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h1 i
    obtain ⟨b', hb'⟩ := exists_frob_basis p b
    exact ⟨b', isLatOf_frob C p L i b b' hb' hb⟩
  · obtain ⟨b', hb'⟩ := exists_frob_basis p b₀
    refine ⟨b', hfin.subset fun i hi => ?_⟩
    intro h
    exact absurd (isLatOf_frob C p L i b₀ b' hb' h) hi

theorem deg_frobLat : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)), IsBun C L →
      IsBun C (frobLat C p L) ∧ deg C (frobLat C p L) = p * deg C L := by
  intro K _ C p _ _ d L hL
  have hL' := isBun_frobLat C p L hL
  refine ⟨hL', ?_⟩
  choose b hb using hL.1
  choose b' hb' using fun i => exists_frob_basis p (b i)
  have e : Fin d ≃ Fin (Module.finrank K (Fin d → K)) := finCongr (Module.finrank_fin_fun K).symm
  set b₀ := (Pi.basisFun K (Fin d)).reindex e with hb₀
  have hdet : ∀ i, b₀.det (b' i) = (b₀.det (b i)) ^ p := by
    intro i
    rw [hb₀, Module.Basis.det_reindex, Module.Basis.det_reindex]
    have hc : (⇑(b' i) ∘ ⇑e) = fun q => frobVec p ((⇑(b i) ∘ ⇑e) q) := by
      funext q; exact hb' i (e q)
    rw [hc, det_frobVec]
  obtain ⟨-, h1⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (Fin d → K) L _ b₀ b hL hb
  obtain ⟨-, h2⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (Fin d → K) (frobLat C p L) _ b₀ b' hL'
    (fun i => isLatOf_frob C p L i (b i) (b' i) (hb' i) (hb i))
  rw [h1, h2, mul_finsum]
  refine finsum_congr fun i => ?_
  rw [hdet, map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Crv.DegFrob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionInjective
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.Induced

theorem isHopfOrder_indOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  classical
  intro R _ _ T _ _ H _ ι hι A hA
  obtain ⟨hfin, hproj, hfull, hcomul, hinv⟩ := hA
  unfold prodSpan at hcomul
  have hmemInd : ∀ f : T → R, f ∈ indOrder ι A ↔ ∀ t : T, (fun h => f (t * ι h)) ∈ A := by
    intro f
    unfold indOrder
    exact Iff.rfl
  have hTr : ∀ g ∈ A, ∀ h0 : H, (fun h => g (h * h0)) ∈ A := by
    intro g hg h0
    obtain ⟨E, hE⟩ : ∃ E : (H × H → R) →ₗ[R] (H → R), ∀ φ h, E φ h = φ (h, h0) :=
      ⟨{ toFun := fun φ h => φ (h, h0)
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }, fun _ _ => rfl⟩
    have hle : Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z : H × H => a z.1 * b z.2} ≤
        (Subalgebra.toSubmodule A).comap E := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      have hEab : E (fun z : H × H => a z.1 * b z.2) = b h0 • a := by
        funext h
        rw [hE]
        simp [mul_comm]
      show E _ ∈ Subalgebra.toSubmodule A
      rw [hEab]
      exact A.smul_mem ha _
    have h1 := hle (hcomul g hg)
    have h2 : E (fun z : H × H => g (z.1 * z.2)) = fun h => g (h * h0) := funext fun h => hE _ h
    rw [Submodule.mem_comap, h2] at h1
    simpa using h1
  have hs : Function.Surjective (QuotientGroup.mk : T → T ⧸ ι.range) := QuotientGroup.mk_surjective
  have hQfin : Finite (T ⧸ ι.range) := Finite.of_surjective _ hs
  let _ : Fintype (T ⧸ ι.range) := Fintype.ofFinite _
  obtain ⟨σ, hσ⟩ : ∃ σ : T ⧸ ι.range → T, ∀ c, (σ c : T ⧸ ι.range) = c :=
    ⟨Function.surjInv hs, Function.surjInv_eq hs⟩
  have hmem : ∀ t : T, (σ (t : T ⧸ ι.range))⁻¹ * t ∈ ι.range := fun t => QuotientGroup.eq.mp (hσ _)
  choose δ hδ using fun t : T => MonoidHom.mem_range.mp (hmem t)
  have hdec : ∀ t : T, σ (t : T ⧸ ι.range) * ι (δ t) = t := fun t => by
    rw [hδ, mul_inv_cancel_left]
  have hmk : ∀ (t : T) (h : H), ((t * ι h : T) : T ⧸ ι.range) = (t : T ⧸ ι.range) := by
    intro t h
    apply QuotientGroup.eq.mpr
    rw [mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem (MonoidHom.mem_range.mpr ⟨h, rfl⟩)
  have hδmul : ∀ (t : T) (h : H), δ (t * ι h) = δ t * h := by
    intro t h
    apply hι
    rw [hδ, map_mul, hδ, hmk, mul_assoc]
  obtain ⟨e, he⟩ : ∃ e : T ⧸ ι.range → T → R,
      ∀ c t, e c t = if (t : T ⧸ ι.range) = c then 1 else 0 :=
    ⟨fun c t => if (t : T ⧸ ι.range) = c then 1 else 0, fun _ _ => rfl⟩
  have he_self : ∀ t : T, e (t : T ⧸ ι.range) t = 1 := fun t => by rw [he, if_pos rfl]
  have he_ne : ∀ (c : T ⧸ ι.range) (t : T), c ≠ (t : T ⧸ ι.range) → e c t = 0 :=
    fun c t hc => by rw [he, if_neg (fun h => hc h.symm)]
  have he_mk : ∀ (c : T ⧸ ι.range) (t : T) (h : H), e c (t * ι h) = e c t :=
    fun c t h => by rw [he, he, hmk]
  let i : (indOrder ι A) →ₗ[R] (T ⧸ ι.range → A) :=
    { toFun := fun f c => ⟨fun h => (f : T → R) (σ c * ι h), (hmemInd _).mp f.2 (σ c)⟩
      map_add' := fun f g => by
        funext c
        apply Subtype.ext
        rfl
      map_smul' := fun r f => by
        funext c
        apply Subtype.ext
        rfl }
  have hp : ∀ a : T ⧸ ι.range → A,
      (fun t : T => ((a (t : T ⧸ ι.range) : A) : H → R) (δ t)) ∈ indOrder ι A := by
    intro a
    rw [hmemInd]
    intro t
    have heq : (fun h => ((a ((t * ι h : T) : T ⧸ ι.range) : A) : H → R) (δ (t * ι h))) =
        fun h => ((a (t : T ⧸ ι.range) : A) : H → R) (h * δ t) := by
      funext h
      rw [hmk, hδmul, mul_comm (δ t) h]
    show (fun h => ((a ((t * ι h : T) : T ⧸ ι.range) : A) : H → R) (δ (t * ι h))) ∈ A
    rw [heq]
    exact hTr _ (a _).2 _
  let p : (T ⧸ ι.range → A) →ₗ[R] (indOrder ι A) :=
    { toFun := fun a => ⟨fun t : T => ((a (t : T ⧸ ι.range) : A) : H → R) (δ t), hp a⟩
      map_add' := fun a b => by
        apply Subtype.ext
        rfl
      map_smul' := fun r a => by
        apply Subtype.ext
        rfl }
  have hpi' : ∀ f, p (i f) = f := by
    intro f
    apply Subtype.ext
    funext t
    show (f : T → R) (σ (t : T ⧸ ι.range) * ι (δ t)) = (f : T → R) t
    rw [hdec]
  have hpi : p.comp i = LinearMap.id := LinearMap.ext hpi'
  have := hfin
  have := hproj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Module.Finite.of_surjective p (fun f => ⟨i f, hpi' f⟩)
  · have hQM : Module.Projective R (T ⧸ ι.range → A) := by
      obtain ⟨M, _, _, _, i0, s0, hs0⟩ := Module.Projective.iff_split.mp hproj
      refine Module.Projective.of_split
        ({ toFun := fun g c => i0 (g c)
           map_add' := fun g g' => by
             funext c
             simp
           map_smul' := fun r g => by
             funext c
             simp } : (T ⧸ ι.range → A) →ₗ[R] (T ⧸ ι.range → M))
        ({ toFun := fun g c => s0 (g c)
           map_add' := fun g g' => by
             funext c
             simp
           map_smul' := fun r g => by
             funext c
             simp } : (T ⧸ ι.range → M) →ₗ[R] (T ⧸ ι.range → A)) ?_
      apply LinearMap.ext
      intro g
      funext c
      show s0 (i0 (g c)) = g c
      exact LinearMap.congr_fun hs0 (g c)
    exact Module.Projective.of_split i p hpi
  · obtain ⟨d, hd0, hd⟩ := hfull
    exact ⟨d, hd0, fun f => (hmemInd _).mpr fun t => hd (fun h => f (t * ι h))⟩
  · intro f hf
    unfold prodSpan
    have hind : ∀ (c : T ⧸ ι.range), ∀ a ∈ A, (fun t => e c t * a (δ t)) ∈ indOrder ι A := by
      intro c a ha
      rw [hmemInd]
      intro t
      have heq : (fun h => e c (t * ι h) * a (δ (t * ι h))) = fun h => e c t * a (h * δ t) := by
        funext h
        rw [he_mk, hδmul, mul_comm (δ t) h]
      show (fun h => e c (t * ι h) * a (δ (t * ι h))) ∈ A
      rw [heq]
      exact A.smul_mem (hTr a ha (δ t)) (e c t)
    obtain ⟨L, hL⟩ : ∃ L : T ⧸ ι.range → T ⧸ ι.range → (H × H → R) →ₗ[R] (T × T → R),
        ∀ c1 c2 φ z, L c1 c2 φ z = e c1 z.1 * e c2 z.2 * φ (δ z.1, δ z.2) :=
      ⟨fun c1 c2 =>
        { toFun := fun φ z => e c1 z.1 * e c2 z.2 * φ (δ z.1, δ z.2)
          map_add' := fun φ ψ => by
            funext z
            simp only [Pi.add_apply]
            ring
          map_smul' := fun r φ => by
            funext z
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            ring },
        fun _ _ _ _ => rfl⟩
    have hsum : (fun z : T × T => f (z.1 * z.2)) =
        ∑ c1 : T ⧸ ι.range, ∑ c2 : T ⧸ ι.range,
          L c1 c2 (fun z : H × H => f (σ c1 * σ c2 * ι (z.1 * z.2))) := by
      funext z
      rw [Finset.sum_apply, Fintype.sum_eq_single (z.1 : T ⧸ ι.range)]
      · rw [Finset.sum_apply, Fintype.sum_eq_single (z.2 : T ⧸ ι.range)]
        · rw [hL]
          try dsimp only
          rw [he_self, he_self, one_mul, one_mul, map_mul, mul_mul_mul_comm, hdec, hdec]
        · intro c2 hc2
          rw [hL, he_ne _ _ hc2, mul_zero, zero_mul]
      · intro c1 hc1
        rw [Finset.sum_apply]
        apply Finset.sum_eq_zero
        intro c2 _
        rw [hL, he_ne _ _ hc1, zero_mul, zero_mul]
    rw [hsum]
    refine sum_mem fun c1 _ => sum_mem fun c2 _ => ?_
    have hle : Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z : H × H => a z.1 * b z.2} ≤
        (Submodule.span R {g | ∃ a ∈ indOrder ι A, ∃ b ∈ indOrder ι A,
          g = fun z : T × T => a z.1 * b z.2}).comap (L c1 c2) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, b, hb, rfl⟩
      show L c1 c2 _ ∈ Submodule.span R _
      apply Submodule.subset_span
      refine ⟨_, hind c1 a ha, _, hind c2 b hb, ?_⟩
      funext z
      rw [hL]
      dsimp only
      ring
    exact hle (hcomul _ ((hmemInd f).mp hf (σ c1 * σ c2)))
  · intro f hf
    rw [hmemInd] at hf ⊢
    intro t
    have heq : (fun h => f ((t * ι h)⁻¹)) = fun h => f (t⁻¹ * ι h⁻¹) := by
      funext h
      rw [map_inv, mul_inv]
    show (fun h => f ((t * ι h)⁻¹)) ∈ A
    rw [heq]
    exact hinv _ (hf t⁻¹)

end GlobalTheory.CompanionTheory.Ar.BT.Induced
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealDescendingOneDimQuotient
section
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal

theorem exists_colength_one (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A]
    (χ : A →ₐ[k] k) (e : A) (J : Ideal A) (he : IsIdempotentElem e) (hχ : χ e = 1)
    (hnil : ∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) (hJe : J ≤ Ideal.span {e}) (hJ0 : J ≠ ⊥) :
    ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧
      (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧
      (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  classical
  set m := RingHom.ker χ with hm
  have hfix : ∀ a ∈ J, e * a = a := by
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp (hJe ha)
    calc e * (x * e) = x * (e * e) := by ring
      _ = x * e := by rw [he.eq]
  have hJ : ¬ J ≤ m * J := by
    intro hle
    have hfg : (J : Submodule A A).FG := IsNoetherian.noetherian J
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
      (J : Submodule A A) hfg (by rwa [Ideal.smul_eq_mul])
    apply hJ0
    rw [eq_bot_iff]
    intro a ha
    have hs : 1 - r ∈ m := by
      have := m.neg_mem hr
      rwa [neg_sub] at this
    have hsa : (1 - r) * a = a := by
      have h0 : r * a = 0 := by simpa [smul_eq_mul] using hr0 a ha
      rw [sub_mul, one_mul, h0, sub_zero]
    have hpow : ∀ n : ℕ, (e * (1 - r)) ^ n * a = a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (e * (1 - r)) ^ (n + 1) * a = (e * (1 - r)) ^ n * (e * ((1 - r) * a)) := by ring
          _ = a := by rw [hsa, hfix a ha, ih]
    obtain ⟨n, hn⟩ := hnil (1 - r) hs
    rw [Ideal.mem_bot, ← hpow n, hn, zero_mul]
  obtain ⟨t, htJ, htW⟩ := SetLike.not_le_iff_exists.mp hJ
  let W : Submodule k A := (m * J).restrictScalars k
  have hq : W.mkQ t ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact htW
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ W), φ (W.mkQ t) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp hcon)
  set l : A →ₗ[k] k := (φ (W.mkQ t))⁻¹ • (φ ∘ₗ W.mkQ) with hl
  have hlt : l t = 1 := by
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, inv_mul_cancel₀ hφ]
  have hlW : ∀ a ∈ m * J, l a = 0 := by
    intro a ha
    have : W.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ha
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, this, map_zero, smul_zero]
  have hdec : ∀ r : A, r - algebraMap k A (χ r) ∈ m := by
    intro r
    rw [hm, RingHom.mem_ker]
    simp
  let J₁ : Ideal A :=
    { carrier := {a | a ∈ J ∧ l a = 0}
      add_mem' := fun {a b} ha hb => ⟨J.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨J.zero_mem, map_zero l⟩
      smul_mem' := fun c a ha => by
        refine ⟨J.mul_mem_left c ha.1, ?_⟩
        have hsplit : c * a = χ c • a + (c - algebraMap k A (χ c)) * a := by
          rw [Algebra.smul_def]
          ring
        change l (c * a) = 0
        rw [hsplit, map_add, map_smul, ha.2, smul_zero, zero_add]
        exact hlW _ (Ideal.mul_mem_mul (hdec c) ha.1) }
  have hmemJ₁ : ∀ a, a ∈ J₁ ↔ a ∈ J ∧ l a = 0 := fun a => Iff.rfl
  refine ⟨J₁, t, l, ?_, htJ, ?_, ?_, ?_, hlt⟩
  · rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun a ha => ((hmemJ₁ a).mp ha).1, t, htJ, fun h => ?_⟩
    have := ((hmemJ₁ t).mp h).2
    rw [hlt] at this
    exact one_ne_zero this
  · intro a ha
    refine ⟨l a, (hmemJ₁ _).mpr ⟨J.sub_mem ha (J.mul_mem_left _ htJ), ?_⟩⟩
    rw [← Algebra.smul_def, map_sub, map_smul, hlt, smul_eq_mul, mul_one, sub_self]
  · intro a ha
    exact (hmemJ₁ _).mpr ⟨J.mul_mem_left a htJ, hlW _ (Ideal.mul_mem_mul ha htJ)⟩
  · intro a ha
    exact ((hmemJ₁ a).mp ha).2

end GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralClosurePlaceRingsData
section
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_of_pow_mem_of_integrally_closed {Ω : Type} [Field Ω] (R : Subring Ω)
    (hR : ∀ z : Ω, IsIntegral R z → z ∈ R) {z : Ω} {m : ℕ} (hm : 0 < m) (h : z ^ m ∈ R) :
    z ∈ R := by
  refine hR z ⟨Polynomial.X ^ m - Polynomial.C ⟨z ^ m, h⟩, Polynomial.monic_X_pow_sub_C _ hm.ne', ?_⟩
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  exact sub_eq_zero.2 rfl

theorem valuation_pow_zpow_eq_of_mul_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {π α : F} {n k : ℤ} {m M : ℕ} (hπ : v.valuation F π = WithZero.exp (-1 : ℤ))
    (hα : v.valuation F α = WithZero.exp (-k)) (h : n * M = m * k) :
    v.valuation F ((π ^ n) ^ M) = v.valuation F (α ^ m) := by
  rw [map_pow, map_zpow₀, hπ, map_pow, hα, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul]
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul]
  linear_combination -h

theorem exists_global_generator : ∀ (F Ω X : Type) [Field F] [NumberField F] [Field Ω] (φ : F →+* Ω) (R : X → Subring Ω) (s : X → Ω) (pl : X → Option (HeightOneSpectrum (𝓞 F))) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ x, ∀ z : Ω, IsIntegral (R x) z → z ∈ R x) → (∀ x, pl x = none → (∀ a : F, φ a ∈ R x) ∧ s x ∈ R x ∧ s x ≠ 0 ∧ (s x)⁻¹ ∈ R x) → (∀ x v, pl x = some v → (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ R x) ∧ ∃ (m : ℕ) (n : ℤ) (π : F), 0 < m ∧ (n : ℚ) = m * r v ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ s x ≠ 0 ∧ s x ^ m / φ π ^ n ∈ R x ∧ φ π ^ n / s x ^ m ∈ R x) → ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧ v.valuation F α = WithZero.exp (-n)) ∧ ∀ x, s x ^ M / φ α ∈ R x ∧ φ α / s x ^ M ∈ R x := by
  intro F Ω X _ _ _ φ R s pl r hR hgen hsp
  obtain ⟨M, α, hM, hα0, hval⟩ := exists_pow_principal F r
  refine ⟨M, α, hM, hα0, hval, fun x => ?_⟩
  cases hx : pl x with
  | none =>
    obtain ⟨hφ, hs, -, hsi⟩ := hgen x hx
    have hαi : (φ α)⁻¹ ∈ R x := by
      rw [← map_inv₀]
      exact hφ _
    constructor
    · rw [div_eq_mul_inv]
      exact (R x).mul_mem ((R x).pow_mem hs M) hαi
    · rw [div_eq_mul_inv, ← inv_pow]
      exact (R x).mul_mem (hφ α) ((R x).pow_mem hsi M)
  | some v =>
    obtain ⟨hφ, m, n, π, hm, hn, hπ, hs0, h1, h2⟩ := hsp x v hx
    obtain ⟨k, hk, hαv⟩ := hval v
    have hkey : n * (M : ℤ) = m * k := by
      have : ((n * M : ℤ) : ℚ) = ((m * k : ℤ) : ℚ) := by
        push_cast
        rw [hn, hk]
        ring
      exact_mod_cast this
    have hv := valuation_pow_zpow_eq_of_mul_eq v hπ hαv hkey
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact WithZero.coe_ne_zero hπ.symm
    have hφπ : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
    have hφα : φ α ≠ 0 := (map_ne_zero φ).2 hα0
    have hP : φ π ^ n ≠ 0 := zpow_ne_zero _ hφπ
    have hβ : v.valuation F ((π ^ n) ^ M / α ^ m) = 1 := by
      rw [map_div₀, hv, div_self]
      exact (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hα0)
    have hβ1 : φ ((π ^ n) ^ M / α ^ m) ∈ R x := hφ _ hβ.le
    have hβ2 : φ ((π ^ n) ^ M / α ^ m)⁻¹ ∈ R x := hφ _ (by rw [map_inv₀, hβ, inv_one])
    constructor
    · apply mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm
      have he : (s x ^ M / φ α) ^ m = (s x ^ m / φ π ^ n) ^ M * φ ((π ^ n) ^ M / α ^ m) := by
        simp only [map_div₀, map_pow, map_zpow₀]
        rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, div_mul_div_comm,
          mul_comm (s x ^ (m * M)), mul_div_mul_left _ _ (pow_ne_zero _ hP)]
      rw [he]
      exact (R x).mul_mem ((R x).pow_mem h1 M) hβ1
    · apply mem_of_pow_mem_of_integrally_closed (R x) (hR x) hm
      have he : (φ α / s x ^ M) ^ m = (φ π ^ n / s x ^ m) ^ M * φ ((π ^ n) ^ M / α ^ m)⁻¹ := by
        simp only [map_inv₀, map_div₀, map_pow, map_zpow₀]
        rw [div_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm M m, inv_div, div_mul_div_comm,
          mul_comm ((φ π ^ n) ^ M), mul_div_mul_right _ _ (pow_ne_zero _ hP)]
      rw [he]
      exact (R x).mul_mem ((R x).pow_mem h2 M) hβ2

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeSummand
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem summand_baseChange : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] (b : V →ₗ[Ω] Vc), IsBaseChange C b → ∀ (L : AddSubgroup V) (U : Submodule Ω V), (∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) → Summand L U → Summand (spanOver RC (b '' L)) (Submodule.span C (b '' U)) ∧ spanOver RC (b '' L) ⊓ (Submodule.span C (b '' U)).toAddSubgroup = spanOver RC (b '' (L ⊓ U.toAddSubgroup : AddSubgroup V)) :=
  @PositivityTheory.Xgn.t_summand_bc

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeSummandCriterion
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem summand_of_locFree_quot : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {V : Type} [AddCommGroup V] [Module Ω V] (U : Submodule Ω V) (N m : ℕ) (L : AddSubgroup V), LocFree R N L → (LocFree R m (L.map U.mkQ.toAddMonoidHom) → Summand L U) ∧ (Summand L U → LocFree R (Module.finrank Ω U) (L.comap U.subtype.toAddMonoidHom) ∧ LocFree R (N - Module.finrank Ω U) (L.map U.mkQ.toAddMonoidHom)) :=
  @PositivityTheory.Xgn.summand_iff_locFree_quot

end GlobalTheory.CompanionTheory.Ar.Num
end

