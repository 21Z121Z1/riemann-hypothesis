import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemDualCuspCharacterLatticeIffAdaptedBasis
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem mem_crdI_one_iff_of_adapted {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
    {X : Data E r} (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E)
    (h : ∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) (v : Fin ρ → E) :
    v ∈ FJ.crdI 1 cu ↔ ∀ b, v b ∈ cc' b := by
  constructor
  · intro hv
    unfold FJ.crdI at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, hax⟩ := hv
      rw [← h, ← hax]
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 (FractionalIdeal.mem_coe.1 ha)
      rw [algebraMap_smul]
      exact X.Λ.smul_mem o hx.1
    | zero => exact fun b => (cc' b).zero_mem
    | add x y _ _ hx hy =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 (hx b)) (FractionalIdeal.mem_coe.2 (hy b)))
    | smul c x _ hx =>
      exact fun b => FractionalIdeal.mem_coe.1
        (Submodule.smul_mem _ c (FractionalIdeal.mem_coe.2 (hx b)))
  · intro hv
    refine Submodule.subset_span ⟨1, FractionalIdeal.mem_coe.2 (FractionalIdeal.one_mem_one _),
      ∑ i, v i • cu.e i, ⟨(h v).2 hv, ?_⟩, one_smul _ _⟩
    exact (show ∑ i, v i • cu.e i ∈ Submodule.span E (Set.range cu.e) from
      sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem mem_dualOE_xcFD_one_iff_of_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ u : Fin ρ → E, u ∈ FJ.dualOE (FJ.XcFD 1 cu) ↔ ∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E) := by
  intro E _ _ _ r ρ X cu cc' h u
  have hc := mem_crdI_one_iff_of_adapted cu cc' h
  constructor
  · intro hu a y hy
    have hm : (Pi.single a y : Fin ρ → E) ∈ FJ.XcFD 1 cu := by
      refine Submodule.subset_span fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (x a) ((hc x).1 hx a)
      refine ⟨n, ?_⟩
      rw [← hn]
      congr 1
      simp [Pi.single_apply]
    have h2 := hu _ hm
    simpa [Pi.single_apply] using h2
  · intro hu x hx
    change ∑ i, u i * x i ∈ (algebraMap (𝓞 E) E).range
    unfold FJ.XcFD at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      refine sum_mem fun i _ => hu i (x i) fun a' ha' => ?_
      have hm : (Pi.single i a' : Fin ρ → E) ∈ FJ.crdI 1 cu := by
        rw [hc]
        intro b
        by_cases hb : b = i
        · subst hb; simpa using ha'
        · rw [Pi.single_eq_of_ne hb]; exact (cc' b).zero_mem
      obtain ⟨n, hn⟩ := hx _ hm
      refine ⟨n, ?_⟩
      rw [hn]
      congr 1
      simp [Pi.single_apply]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul c x _ hx =>
      have e : ∑ i, u i * (c • x) i = algebraMap (𝓞 E) E c * ∑ i, u i * x i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def]; ring
      rw [e]
      exact mul_mem ⟨c, rfl⟩ hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PerFrLact
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PerGam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma perFr_lact (X : Data E r) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (lact γ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = perFr X x v τ i := by
  have hm : ∀ t : X.Ψ, mat (lact γ x) t = (γ : Matrix (Fin r) (Fin r) E).map t.1 * mat x t := fun _ => rfl
  have hu : ∀ t : E →+* ℂ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map t).det := fun t =>
    (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map t.mapMatrix)
  unfold perFr
  simp only [hm, GlobalTheory.PerMove.emb_mulVec]
  split_ifs
  · rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hu _),
      Matrix.mul_one]
  · rfl
  · rw [GlobalTheory.PerMove.col_mul, GlobalTheory.PerMove.hermC_unitary _ _ _ hγ]
  · rfl
  · rfl

omit [IsCMField E] in

lemma exists_equiv (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (hγ : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ Λ) :
    ∃ f : Λ ≃ₗ[𝓞 E] Λ, ∀ a, (f a : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) := by
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨{ toFun := fun a => ⟨(γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E), (hγ _).1 a.2⟩
            invFun := fun a => ⟨((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E),
              (hγ _).2 (by rw [hri]; exact a.2)⟩
            map_add' := fun a b => Subtype.ext (by simp [Matrix.mulVec_add])
            map_smul' := fun s a => Subtype.ext (by simp [Matrix.mulVec_smul])
            left_inv := fun a => Subtype.ext (hli _)
            right_inv := fun a => Subtype.ext (hri _) }, fun _ => rfl⟩

end GlobalTheory.PerGam

namespace GlobalTheory

theorem per_gam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ γ ∈ (M.X k).Γ, ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La, ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) ∧ ∀ x ∈ (M.X k).dom, ∀ a, Pf (lact γ x) (gam a) = Pf x a := by
  intro E _ _ _ H Dw l Xo c σ g e F r M _ hB _ k Pf hP γ hγ
  obtain ⟨⟨hU, hS⟩, hM, hA⟩ := (hB.gam k γ).1 hγ
  obtain ⟨f, hf⟩ := PerGam.exists_equiv _ γ hS
  let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La := (M.φ k).trans (f.trans (M.φ k).symm)
  have hg : ∀ a, (M.φ k (gam a) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
    intro a
    rw [← hf]
    simp [gam]
  have key : ∀ (n : ℕ) (a b : (F.Di k).La),
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + n • (M.φ k b : Fin r → E) → gam a = a + n • b := by
    intro n a b h
    apply (M.φ k).injective
    apply Subtype.ext
    rw [hg, h, map_add, map_nsmul]
    rfl
  refine ⟨gam, ⟨fun a b => ?_, fun a ha => ?_, fun a => ?_⟩, fun x _ a => ?_⟩
  · have h1 := hB.ef k (gam a) (gam b)
    rw [hg, hg, hU, ← hB.ef k a b] at h1
    exact_mod_cast h1
  · obtain ⟨b, hb⟩ := hM a ha
    exact ⟨b, key _ a b hb⟩
  · obtain ⟨b, hb⟩ := hA a
    exact ⟨b, key _ a b hb⟩
  · funext j
    rw [hP, hP, hg, PerGam.perFr_lact _ γ hU]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.Relab

theorem relab_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → Function.Bijective (relab c σ) ∧ (∀ τ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0) ∧ (∀ τ, relab c σ (conjEmb τ) = conjEmb (relab c σ τ)) ∧ ∀ (Dw : Datum H) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  intro E _ _ _ H l c σ hσ
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ' : E →+* ℂ, (relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0) := by
    intro τ'
    have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
    have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
    · refine ⟨fun _ => hx, fun _ => ?_⟩
      rw [hval, ← hσ0]
      exact congrArg σ (Subtype.ext hx)
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · exfalso
        have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
          rw [← map_neg]
          exact congrArg σ (Subtype.ext hx)
        rw [← hval, h, hσ0] at h1
        exact h0 (by linear_combination h1 / 2)
      · exfalso
        exact h0 (by linear_combination (h.symm.trans hx) / 2)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  refine ⟨⟨hinj, hsurj⟩, hrel, ?_, ?_⟩
  · intro τ
    ext a
    have key : ∀ (ρ : E →+* ℂ) (x : E), conjEmb ρ x = ρ (IsCMField.complexConj E x) := fun ρ x =>
      (IsCMField.complexEmbedding_complexConj E ρ x).symm
    rw [key]
    exact congrArg σ (Subtype.ext (key τ a))
  · intro Dw g e τ
    obtain ⟨τ₀, rfl⟩ := hsurj τ
    have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
      have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
        Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
      have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
        e.subtypeEquiv (fun _ => Iff.rfl)
      have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} ≃ Fin (Dw.mult τ₀) := Equiv.sigmaSubtype τ₀
      rw [Nat.card_congr (e1.trans (e2.trans e3)), Nat.card_eq_fintype_card, Fintype.card_fin]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [hcard]
      unfold Datum.mult
      rw [if_pos ((hrel τ₀).1 h)]
    · rw [hcard]
      unfold Datum.mult
      rw [if_neg (fun h' => h ((hrel τ₀).2 h'))]

end GlobalTheory.Relab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledBaseChange_fibreSection_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T U : Type) [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X) (x'' : Sp U ⟶ Xo.X), x' = spMap φ ≫ x → x'' = spMap ψ ≫ x' → (∀ (a : S) s s' s'', SecBC φ a x x' s s' → (SecBC ψ 1 x' x'' s' s'' ↔ SecBC (ψ.comp φ) a x x'' s s'')) ∧ (∀ (a : S) (s t : LB.Sec (PPx x)), SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i) ∧ (∀ (a : S) s (s' t' : LB.Sec (PPx x')), SecBC φ 1 x x' s s' → (SecBC φ a x x' s t' ↔ ∀ i, t'.f i = scal x' (φ a) i * s'.f i)) ∧ (∀ (a b : S) i, scal x (a * b) i = scal x a i * scal x b i ∧ scal x (a + b) i = scal x a i + scal x b i ∧ scal x 1 i = 1) := by
  first | exact @GlobalTheory.Frames.SecCalc.sec_calc | exact GlobalTheory.Frames.SecCalc.sec_calc | (intros; apply GlobalTheory.Frames.SecCalc.sec_calc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s s', SecBC φ 1 x x' s s' → ∀ p' : Sp T, (∃ (q : Gx x') (i : (PPx x').ι), Formalism.L2.PjFree.gxSnd x' q = p' ∧ q ∈ (Gx x').basicOpen (s'.f i)) ↔ ∃ (q : Gx x) (i : (PPx x).ι), Formalism.L2.PjFree.gxSnd x q = spMap φ p' ∧ q ∈ (Gx x).basicOpen (s.f i) := by
  first | exact @GlobalTheory.Frames.secBC_nonvanishing_iff | exact GlobalTheory.Frames.secBC_nonvanishing_iff | (intros; apply GlobalTheory.Frames.secBC_nonvanishing_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FlagData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem transvMat_mulVec (G : Matrix (Fin r) (Fin r) E) (ξ x : Fin r → E) (α : E) :
    FD.transvMat G ξ α *ᵥ x = x + (α * FD.herm G x ξ) • ξ := by
  funext a
  simp only [FD.transvMat, FD.herm, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem herm_add_smul_left (G : Matrix (Fin r) (Fin r) E) (x ξ y : Fin r → E) (c : E) :
    FD.herm G (x + c • ξ) y = FD.herm G x y + c * FD.herm G ξ y := by
  simp only [FD.herm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_add_smul_right (G : Matrix (Fin r) (Fin r) E) (x ξ y : Fin r → E) (c : E) :
    FD.herm G x (y + c • ξ) = FD.herm G x y + FD.cc c * FD.herm G x ξ := by
  simp only [FD.herm, FD.cc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_add,
    map_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem cc_herm {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (x y : Fin r → E) : FD.cc (FD.herm G x y) = FD.herm G y x := by
  have hG' : ∀ a b, IsCMField.complexConj E (G a b) = G b a := hG
  simp only [FD.herm, FD.cc, map_sum, map_mul, hG', IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem transvMat_mul_neg (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : FD.transvMat G ξ α * FD.transvMat G ξ (-α) = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, hξ, mul_zero, add_zero, neg_mul,
    neg_smul, neg_add_cancel_right]

noncomputable def transv (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : GL (Fin r) E where
  val := FD.transvMat G ξ α
  inv := FD.transvMat G ξ (-α)
  val_inv := transvMat_mul_neg G hξ α
  inv_val := by simpa using transvMat_mul_neg G hξ (-α)

theorem herm_transvMat {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0) {α : E} (hα : FD.cc α = -α) (x y : Fin r → E) :
    FD.herm G (FD.transvMat G ξ α *ᵥ x) (FD.transvMat G ξ α *ᵥ y) = FD.herm G x y := by
  have e : FD.cc (α * FD.herm G y ξ) = -α * FD.herm G ξ y := by
    rw [← hα, ← cc_herm hG y ξ]
    exact map_mul (IsCMField.complexConj E) _ _
  rw [transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, herm_add_smul_right,
    herm_add_smul_right, hξ, e]
  ring

omit [NumberField E] [IsCMField E] in
theorem smul_mem_of_isIntegral (Λ : Submodule (𝓞 E) (Fin r → E)) {c : E} (hc : IsIntegral ℤ c)
    {v : Fin r → E} (hv : v ∈ Λ) : c • v ∈ Λ :=
  Λ.smul_mem (⟨c, hc⟩ : 𝓞 E) hv

theorem exists_data : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 M m : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (ξ0 κ0 : E), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ a b, FD.cc (Gm a b) = Gm b a) → Gm.det ≠ 0 → p0 ≤ r → (∀ τ ∈ Ψ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → 3 ≤ M → FD.cc ξ0 = -ξ0 → ξ0 ≠ 0 → (κ0 = 2 * ξ0 ∨ κ0 = -(2 * ξ0)) → (∀ τ ∈ Ψ, (τ κ0).im < 0) → 0 < m → (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) / (M : E) * κ0 * FD.herm Gm x y)) → ∃ X : FD.Data E r, X.Ψ = Ψ ∧ X.Gm = Gm ∧ X.p0 = p0 ∧ X.Λ = Λ ∧ X.ξ0 = ξ0 ∧ X.κ0 = κ0 ∧ X.m = m ∧ (∀ γ, γ ∈ X.Γ ↔ FD.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∀ la γ, X.χ la γ = 1 := by
  intro hMink E _ _ _ r p0 M m Ψ Gm Λ ξ0 κ0 hΨ hG hdet hp hsig hfg hsp hM hξ hξ0 hκ hκs hm hint
  obtain ⟨Γ, hΓ, hidx⟩ :=
    GlobalTheory.CongruenceIndex.congruence_finiteIndex E r M Gm Λ hfg (by omega)
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hκ0 : κ0 ≠ 0 := by rcases hκ with h | h <;> simp [h, hξ0]
  have hξ' : IsCMField.complexConj E ξ0 = -ξ0 := hξ
  have hκc : IsCMField.complexConj E κ0 = -κ0 := by
    rcases hκ with h | h <;> simp [h, hξ', map_ofNat]
  have halg : IsAlgebraic ℤ (((m : E) / (M : E) * κ0)⁻¹) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  refine ⟨{
    Ψ := Ψ, cmType := hΨ, Gm := Gm, Gm_herm := hG, Gm_det := hdet, p0 := p0, p0_le := hp
    signature := fun τ => hsig τ.1 τ.2
    Λ := Λ, Λ_fg := hfg, Λ_span := hsp
    den := (k : 𝓞 E), den_ne := Int.cast_ne_zero.2 hk
    Λ_int := fun x hx y hy => ?_
    Γ := Γ, Γ_stab := fun γ h => ((hΓ γ).1 h).1, Γ_index := hidx
    Γ_free := fun γ h => GlobalTheory.GamFree.gam_free hMink E r p0 M Ψ Gm Λ γ hΨ hG hfg hsp hM
      ((hΓ γ).1 h).1 ((hΓ γ).1 h).2
    χ := fun _ _ => 1
    χ_mul := fun _ _ _ _ _ => (mul_one _).symm
    χ_add := fun _ _ _ _ => (mul_one _).symm
    χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow _⟩
    ξ0 := ξ0, ξ0_im := hξ, ξ0_ne := hξ0, κ0 := κ0, κ0_xi := hκ
    κ0_sign := fun τ => hκs τ.1 τ.2
    m := m, m_pos := hm
    transv := fun ξ hξΛ hiso s hs hsi => ?_ },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, hΓ, fun _ _ => rfl⟩
  · have h := hki.mul (hint x hx y hy)
    have e : k • ((m : E) / (M : E) * κ0)⁻¹ * ((m : E) / (M : E) * κ0 * FD.herm Gm x y) =
        (((k : 𝓞 E) : 𝓞 E) : E) * FD.herm Gm x y := by
      rw [zsmul_eq_mul]
      simp only [map_intCast]
      field_simp
    rwa [e] at h
  · have hs' : IsCMField.complexConj E s = s := hs
    have hα : FD.cc ((m : E) * s * κ0) = -((m : E) * s * κ0) := by
      simp [FD.cc, hs', hκc]
    have hMi : IsIntegral ℤ (M : E) := isIntegral_natCast M
    have key : ∀ v ∈ Λ, (s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ ∈ Λ := fun v hv =>
      smul_mem_of_isIntegral Λ (hsi.mul (hint v hv ξ hξΛ)) hξΛ
    have e : ∀ v, ((m : E) * s * κ0 * FD.herm Gm v ξ) • ξ =
        M • ((s * ((m : E) / (M : E) * κ0 * FD.herm Gm v ξ)) • ξ) := by
      intro v
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul]
      congr 1
      field_simp
    refine ⟨transv Gm hiso ((m : E) * s * κ0), (hΓ _).2 ⟨⟨herm_transvMat hG hiso hα, fun x => ?_⟩,
      fun v hv => ⟨_, key v hv, ?_⟩⟩, rfl⟩
    · change x ∈ Λ ↔ FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ x ∈ Λ
      rw [transvMat_mulVec]
      refine ⟨fun hx => Λ.add_mem hx (by rw [e]; exact nsmul_mem (key x hx) M), fun hx => ?_⟩
      have h := nsmul_mem (key _ hx) M
      rw [← e, herm_add_smul_left, hiso, mul_zero, add_zero] at h
      simpa using Λ.sub_mem hx h
    · change FD.transvMat Gm ξ ((m : E) * s * κ0) *ᵥ v = _
      rw [transvMat_mulVec, e]

end GlobalTheory.FlagData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestRingLocalizationAway
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem testRing_localizationAway :
    ∀ (K : Type) [Field K] (p : TRing K) (g : p.R), ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R), IsUnit (lam g) ∧ ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T), IsUnit (ψ g) → ∃ k : p'.R →ₐ[K] T, k.comp lam = ψ := by
  intro K _ p g
  obtain ⟨h1, h2⟩ := reduced_finiteType_iff_testRing K
  obtain ⟨hft, hred⟩ := h2 p
  have hft1 : Algebra.FiniteType p.R (Localization.Away g) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) _
  have hft' : Algebra.FiniteType K (Localization.Away g) := Algebra.FiniteType.trans hft hft1
  have hred' : IsReduced (Localization.Away g) :=
    isReduced_localizationPreserves (Submonoid.powers g) _ hred
  obtain ⟨p', ⟨e⟩⟩ := h1 (Localization.Away g) hft' hred'
  refine ⟨p', e.symm.toAlgHom.comp (IsScalarTower.toAlgHom K p.R (Localization.Away g)), ?_, ?_⟩
  · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map e.symm
  · intro T _ _ ψ hψ
    have hu : ∀ y : Submonoid.powers g, IsUnit (ψ y) := by
      rintro ⟨_, n, rfl⟩
      simpa using hψ.pow n
    refine ⟨(IsLocalization.liftAlgHom (M := Submonoid.powers g) (S := Localization.Away g)
      (f := ψ) hu).comp e.toAlgHom, ?_⟩
    apply AlgHom.ext
    intro x
    simp [IsLocalization.liftAlgHom]

end GlobalTheory
end

