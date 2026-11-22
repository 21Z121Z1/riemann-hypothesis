import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0033
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0023
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplittingFw

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointHol
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.TangentOrigin

namespace GlobalTheory.AnPer

theorem exists_point_hol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens E)
    (X : Scheme.{0}) (e : E → (Sp ℂ ⟶ X)) (U : X.Opens), IsAffineOpen U → IsHolTo (W : Set E) e → (∀ p ∈ W, ⊤ ≤ e p ⁻¹ᵁ U) →
    ∃ x : Sp (Hol W) ⟶ X, ⊤ ≤ x ⁻¹ᵁ U ∧ ∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = e p := by
  intro E _ _ _ W X e U hU he hW
  have ha : ∀ f : Γ(X, U), AnalyticOnNhd ℂ (fun p => valAt' (e p) U f) W := fun f p hp =>
    SCV.analyticAt_of_differentiableOn (he U f).2 ((he U f).1.mem_nhds ⟨hp, hW p hp⟩)
  have hv : ∀ (f : Γ(X, U)) (p : E) (hp : p ∈ W), (Hol.mk _ (ha f)).fn p = evalPt (e p) U (hW p hp) f :=
    fun f p hp => (Hol.fn_mk _ _ hp).trans (valAt'_eq_evalPt _ _ _ _)
  let ψ : Γ(X, U) →+* Hol W :=
    { toFun := fun f => Hol.mk _ (ha f)
      map_one' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_one, ← Hol.ev_apply p hp, map_one]
      map_mul' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_mul _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_mul]
      map_zero' := Hol.ext_fn fun p hp => by rw [hv _ p hp, map_zero, ← Hol.ev_apply p hp, map_zero]
      map_add' := fun f g => Hol.ext_fn fun p hp => by rw [Hol.fn_add _ _ hp, hv _ p hp, hv _ p hp, hv _ p hp, map_add] }
  obtain ⟨x, hx, hxψ⟩ := exists_evalPt_eq hU ψ
  have h' : ∀ (p : E) (hp : p ∈ W), ⊤ ≤ (spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x) ⁻¹ᵁ U := fun p hp q _ => hx trivial
  refine ⟨x, hx, fun p hp => ext_evalPt hU (h' p hp) (hW p hp) (RingHom.ext fun f => ?_)⟩
  rw [evalPt_spMap_comp _ x U hx, hxψ]
  exact (Hol.ev_apply p hp _).trans (hv f p hp)

theorem point_hol_ext : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E)
    (X S : Scheme.{0}) (s : X ⟶ S) [IsSeparated s] (x x' : Sp (Hol W) ⟶ X), x ≫ s = x' ≫ s →
    (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x = spMap (Hol.ev p hp : Hol W →+* ℂ) ≫ x') → x = x' := by
  intro E _ _ W X S s _ x x' hs h
  have : _root_.IsReduced (Hol W) := isReduced_of_injective (holSub W).val Subtype.val_injective
  suffices IsDominant (equalizer.ι x x') from
    ext_of_isDominant_of_isSeparated s hs (equalizer.ι x x') (equalizer.condition _ _)
  refine ⟨?_⟩
  have hd : Dense (Set.range fun p : W => PrimeSpectrum.comap (Hol.ev p.1 p.2 : Hol W →+* ℂ) default) := by
    rw [dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro f hf
    have : f = 0 := Hol.ext_fn fun p hp => by
      have h1 := (PrimeSpectrum.mem_vanishingIdeal _ _).1 hf _ ⟨⟨p, hp⟩, rfl⟩
      have h2 : Hol.ev p hp f ∈ (default : PrimeSpectrum ℂ).asIdeal := h1
      rw [Ideal.eq_bot_of_prime (default : PrimeSpectrum ℂ).asIdeal, Ideal.mem_bot] at h2
      rw [← Hol.ev_apply p hp, ← Hol.ev_apply p hp, h2, map_zero]
    rw [this]
    exact zero_mem _
  refine Dense.mono ?_ hd
  rintro _ ⟨p, rfl⟩
  refine ⟨equalizer.lift _ (h p.1 p.2) (default : PrimeSpectrum ℂ), ?_⟩
  exact congrArg (fun m : Sp ℂ ⟶ Sp (Hol W) => m (default : PrimeSpectrum ℂ)) (equalizer.lift_ι _ (h p.1 p.2))

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointMemTranslates
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedFibre

theorem exists_point_mem_translates :
    ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IrreducibleSpace (Over.mk t ⊗ P.A).left → ∀ (U : (Over.mk t ⊗ P.A).left.Opens),
      (U : Set (Over.mk t ⊗ P.A).left).Nonempty → ∀ (a c : Over.mk t ⟶ P.A) (p : Spec (CommRingCat.of K)),
      ∃ u : Over.mk t ⟶ P.A, (lift (𝟙 (Over.mk t)) (c * u * a)).left p ∈ U ∧
        (lift (𝟙 (Over.mk t)) (u⁻¹ * a)).left p ∈ U := by
  intro S P K _ _ t hirr U hU a c p
  let T : Over S := Over.mk t
  let E : Over S := T ⊗ P.A
  have hsm : Smooth P.A.hom := P.isAb.smooth
  have hlft : LocallyOfFiniteType (fst T P.A).left := by
    change LocallyOfFiniteType (pullback.fst t P.A.hom)
    infer_instance
  have hJ0 : JacobsonSpace T.left := by
    change JacobsonSpace (PrimeSpectrum K)
    infer_instance
  have hJ : JacobsonSpace E.left := LocallyOfFiniteType.jacobsonSpace (fst T P.A).left
  let g₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c) * snd T P.A * (fst T P.A ≫ a))
  let g₂ : E ⟶ E := lift (fst T P.A) ((snd T P.A)⁻¹ * (fst T P.A ≫ a))
  let h₁ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ c)⁻¹ * snd T P.A * (fst T P.A ≫ a)⁻¹)
  let h₂ : E ⟶ E := lift (fst T P.A) ((fst T P.A ≫ a) * (snd T P.A)⁻¹)
  have e₁ : h₁ ≫ g₁ = 𝟙 E := by
    ext1
    · simp [g₁, h₁]
    · simp [g₁, h₁, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have e₂ : h₂ ≫ g₂ = 𝟙 E := by
    ext1
    · simp [g₂, h₂]
    · simp [g₂, h₂, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc]
      exact (Category.id_comp _).symm
  have ne : ∀ {f g : E ⟶ E}, g ≫ f = 𝟙 E → ((f.left ⁻¹ᵁ U : E.left.Opens) : Set E.left).Nonempty := by
    intro f g h
    obtain ⟨w, hw⟩ := hU
    refine ⟨g.left w, ?_⟩
    change f.left (g.left w) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
    exact hw
  have hin := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) (ne e₁) (ne e₂)
  obtain ⟨z, hz, hc⟩ := nonempty_inter_closedPoints hin
    ((TopologicalSpace.Opens.isOpen _).inter (TopologicalSpace.Opens.isOpen _)).isLocallyClosed
  let q := pointOfClosedPoint (fst T P.A).left z hc
  have hq : q ≫ (fst T P.A).left = 𝟙 _ := pointOfClosedPoint_comp _ z hc
  have hqw : q ≫ E.hom = t := by
    rw [← Over.w (fst T P.A), ← Category.assoc, hq, Category.id_comp]
    rfl
  let Q : T ⟶ E := Over.homMk q hqw
  have hQf : Q ≫ fst T P.A = 𝟙 T := by
    ext1
    exact hq
  have hQf' : ∀ (f : T ⟶ P.A), Q ≫ fst T P.A ≫ f = f := fun f => by
    rw [← Category.assoc, hQf, Category.id_comp]
  have hqp : q p = z := pointOfClosedPoint_apply _ z hc p
  refine ⟨Q ≫ snd T P.A, ?_, ?_⟩
  · have hQ : lift (𝟙 T) (c * (Q ≫ snd T P.A) * a) = Q ≫ g₁ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₁, hQf]
      · simp only [lift_snd, Category.assoc, g₁, MonObj.comp_mul, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₁.left (q p) ∈ U
    rw [hqp]
    exact hz.1
  · have hQ : lift (𝟙 T) ((Q ≫ snd T P.A)⁻¹ * a) = Q ≫ g₂ := by
      ext1
      · simp only [lift_fst, Category.assoc, g₂, hQf]
      · simp only [lift_snd, Category.assoc, g₂, MonObj.comp_mul, GrpObj.comp_inv, hQf']
    rw [hQ, Over.comp_left, Scheme.Hom.comp_apply]
    change g₂.left (q p) ∈ U
    rw [hqp]
    exact hz.2

end GlobalTheory.AlgClosedFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepsModKM
section
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UCls.IdxK

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem fv_mem {n : ℕ} {L : Set (Fin n → E)} {t : Fin n → E} (ht : t ∈ L) : fv F t ∈ hat F L :=
  AddSubgroup.subset_closure ⟨1, fun v => one_mem _, t, ht, rfl⟩

theorem fv_add {n : ℕ} (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i; simp [fv, TensorProduct.tmul_add]

theorem fv_nsmul {n : ℕ} (M : ℕ) (x : Fin n → E) : fv F (M • x) = M • fv F x := by
  funext i
  exact map_nsmul (TensorProduct.mk F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) E 1) M (x i)

theorem smul_mem_hat {n : ℕ} {L : Set (Fin n → E)} (hL : ∀ o : 𝓞 E, ∀ x ∈ L, o • x ∈ L)
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) (o : 𝓞 E)
    {z : Fin n → RA F E} (hz : z ∈ hat F L) : (a ⊗ₜ[F] (o : E)) • z ∈ hat F L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, o • x, hL o x hx, ?_⟩
    · exact mul_mem (ha v) (hb v)
    · funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.UCls.IdxK

namespace GlobalTheory.UCls.IdxK

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem cong_of_gens {n M : ℕ} {L : Set (Fin n → E)} (hL : ∀ o : 𝓞 E, ∀ x ∈ L, o • x ∈ L)
    (e : Fin n → Fin n → E)
    (he : ∀ x ∈ L, ∃ o : Fin n → 𝓞 E, ∃ y ∈ L, x = ∑ i, o i • e i + M • y)
    (g s : Matrix (Fin n) (Fin n) (RA F E))
    (hg : ∀ x ∈ hat F L, g *ᵥ x ∈ hat F L) (hs : ∀ x ∈ hat F L, s *ᵥ x ∈ hat F L)
    (hgs : ∀ i, ∃ y ∈ hat F L, g *ᵥ fv F (e i) - s *ᵥ fv F (e i) = M • y) :
    ∀ x ∈ hat F L, ∃ y ∈ hat F L, g *ᵥ x - s *ᵥ x = M • y := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨o, y, hy, rfl⟩ := he x hx
    choose w hw hwe using hgs
    set u : Fin n → RA F E := fun i => a ⊗ₜ[F] y i with hu
    have huH : u ∈ hat F L := AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩
    have key : (fun i => a ⊗ₜ[F] (∑ j, o j • e j + M • y) i) =
        ∑ j, (a ⊗ₜ[F] (o j : E)) • fv F (e j) + M • u := by
      funext i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_add, TensorProduct.tmul_sum, hu]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_mul, fv, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
      · exact map_nsmul (TensorProduct.mk F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) E a) M (y i)
    refine ⟨∑ j, (a ⊗ₜ[F] (o j : E)) • w j + (g *ᵥ u - s *ᵥ u),
      add_mem (sum_mem fun j _ => smul_mem_hat hL ha (o j) (hw j)) (sub_mem (hg u huH) (hs u huH)), ?_⟩
    rw [key, ← Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.sub_mulVec,
      smul_add, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, hwe j, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y1, h1, e1⟩ := hx
    obtain ⟨y2, h2, e2⟩ := hy
    refine ⟨y1 + y2, add_mem h1 h2, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_add, smul_add, ← e1, ← e2]
    abel
  | neg x _ hx =>
    obtain ⟨y1, h1, e1⟩ := hx
    refine ⟨-y1, neg_mem h1, ?_⟩
    rw [Matrix.mulVec_neg, Matrix.mulVec_neg, smul_neg, ← e1]
    abel

theorem isKM_inv_mul {n M : ℕ} {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)}
    {g s : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsKM c G L 1 g) (hs : IsKM c G L 1 s) (hsd : s.det = 1)
    (hgs : ∀ x ∈ hat F L, ∃ y ∈ hat F L, g *ᵥ x - s *ᵥ x = M • y) : IsKM c G L M (s⁻¹ * g) := by
  have hsu : IsUnit s.det := by rw [hsd]; exact isUnit_one
  have hss : ∀ v, s *ᵥ (s⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hsu, Matrix.one_mulVec]
  have hss' : ∀ v, s⁻¹ *ᵥ (s *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hsu, Matrix.one_mulVec]
  have into : ∀ x ∈ hat F L, s *ᵥ x ∈ hat F L := by
    intro x hx
    obtain ⟨y, hy, h⟩ := hs.2.1 x hx
    rw [one_smul] at h
    rw [show s *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv, hsd, Ring.inverse_one, one_mul]
    exact hg.1.1
  · intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hs.1.2 (s⁻¹ *ᵥ (g *ᵥ x)) (s⁻¹ *ᵥ (g *ᵥ y)), hss, hss,
      hg.1.2]
  · intro x hx
    obtain ⟨y, hy, h⟩ := hgs x hx
    obtain ⟨w, hw, rfl⟩ := hs.2.2 y hy
    refine ⟨w, hw, ?_⟩
    have h1 : g *ᵥ x = s *ᵥ (x + M • w) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, ← h]; abel
    rw [← Matrix.mulVec_mulVec, h1, hss']
    abel
  · intro x hx
    obtain ⟨y, hy, h⟩ := hg.2.2 (s *ᵥ x) (into x hx)
    exact ⟨y, hy, by rw [← Matrix.mulVec_mulVec, h, hss']⟩

end GlobalTheory.UCls.IdxK

namespace GlobalTheory.UCls.IdxK

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem hat_approx {n M : ℕ} (hM : 1 ≤ M) {L : Set (Fin n → E)}
    (hL : ∀ b : 𝓞 F, ∀ x ∈ L, algebraMap F E (b : F) • x ∈ L) (hL0 : (0 : Fin n → E) ∈ L)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x + y ∈ L) (hLn : ∀ x ∈ L, -x ∈ L) :
    ∀ z ∈ hat F L, ∃ t ∈ L, ∃ y ∈ hat F L, z = fv F t + M • y := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨b, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F (M : 𝓞 F) (by exact_mod_cast (by omega : M ≠ 0)) a ha
    refine ⟨algebraMap F E (b : F) • x, hL b x hx, fun i => y ⊗ₜ[F] x i,
      AddSubgroup.subset_closure ⟨y, hy, x, hx, rfl⟩, ?_⟩
    funext i
    rw [e]
    simp only [fv, Pi.add_apply, Pi.smul_apply, TensorProduct.add_tmul, smul_eq_mul]
    congr 1
    · rw [show algebraMap (𝓞 F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) b =
          algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (b : F) from rfl,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
    · rw [map_natCast, ← nsmul_eq_mul, TensorProduct.smul_tmul']
  | zero => exact ⟨0, hL0, 0, zero_mem _, by funext i; simp [fv]⟩
  | add x y _ _ hx hy =>
    obtain ⟨t1, ht1, y1, hy1, rfl⟩ := hx
    obtain ⟨t2, ht2, y2, hy2, rfl⟩ := hy
    exact ⟨t1 + t2, hLa _ ht1 _ ht2, y1 + y2, add_mem hy1 hy2, by rw [fv_add, smul_add]; abel⟩
  | neg x _ hx =>
    obtain ⟨t1, ht1, y1, hy1, rfl⟩ := hx
    refine ⟨-t1, hLn _ ht1, -y1, neg_mem hy1, ?_⟩
    rw [neg_add, smul_neg]
    congr 1
    funext i; simp [fv, TensorProduct.tmul_neg]

end GlobalTheory.UCls.IdxK

namespace GlobalTheory.UCls.IdxK

theorem exists_reps_mod_KM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → SelfDualLat G Λ →
    ∃ S : Finset (Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), S.card ≤ M ^ (2 * fdeg E * r ^ 2) ∧
      ∀ g, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g → g.det = 1 →
        ∃ s ∈ S, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 s ∧ s.det = 1 ∧
          ∃ k, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M k ∧ g = s * k := by
  intro E _ _ _ r M G Λ hM hSD
  classical
  have hFG : Λ.FG := hSD.2.2.1
  obtain ⟨e, heΛ, he⟩ := GlobalTheory.T.exists_gens_mod_nsmul_of_fg_numberField E r M Λ hM hFG
  obtain ⟨T, hTc, hTΛ, hT⟩ := GlobalTheory.T.exists_reps_mod_lattice_card_le E r M Λ hM hFG
  have hLo : ∀ o : 𝓞 E, ∀ x ∈ (Λ : Set (Fin r → E)), o • x ∈ (Λ : Set (Fin r → E)) :=
    fun o x hx => Λ.smul_mem o hx
  have hLb : ∀ b : 𝓞 (maximalRealSubfield E), ∀ x ∈ (Λ : Set (Fin r → E)),
      algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E) • x ∈ (Λ : Set (Fin r → E)) := by
    intro b x hx
    have hi : IsIntegral ℤ (algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E)) :=
      b.2.map (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    exact Λ.smul_mem (⟨_, hi⟩ : 𝓞 E) hx
  have hQ : ∀ z ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), ∃ t ∈ T,
      ∃ y ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), z = fv _ t + M • y := by
    intro z hz
    obtain ⟨t0, ht0, y0, hy0, rfl⟩ := hat_approx hM hLb Λ.zero_mem (fun x hx y hy => Λ.add_mem hx hy)
      (fun x hx => Λ.neg_mem hx) z hz
    obtain ⟨t, ht, y1, hy1, rfl⟩ := hT t0 ht0
    refine ⟨t, ht, fv _ y1 + y0, add_mem (fv_mem hy1) hy0, ?_⟩
    rw [fv_add, fv_nsmul, smul_add, add_assoc]
  have into : ∀ g, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g →
      ∀ x ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), g *ᵥ x ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) := by
    intro g hg x hx
    obtain ⟨y, hy, h⟩ := hg.2.1 x hx
    rw [one_smul] at h
    rw [show g *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  let K1 := {g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) //
    IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g ∧ g.det = 1}
  have hex : ∀ g : K1, ∀ i, ∃ t ∈ T, ∃ y ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)),
      g.1 *ᵥ fv _ (e i) = fv _ t + M • y :=
    fun g i => hQ _ (into g.1 g.2.1 _ (fv_mem (heΛ i)))
  choose τ hτT yy hyy hτ using hex
  let σ : (Fin r → Fin r → E) → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) :=
    fun t => if h : ∃ g : K1, τ g = t then h.choose.1 else 1
  refine ⟨(Fintype.piFinset fun _ : Fin r => T).image σ, ?_, ?_⟩
  · calc _ ≤ (Fintype.piFinset fun _ : Fin r => T).card := Finset.card_image_le
      _ = T.card ^ r := by simp
      _ ≤ (M ^ (2 * fdeg E * r)) ^ r := Nat.pow_le_pow_left hTc r
      _ = _ := by rw [← pow_mul]; ring_nf
  · intro g hg hdet
    let g' : K1 := ⟨g, hg, hdet⟩
    have hex' : ∃ g'' : K1, τ g'' = τ g' := ⟨g', rfl⟩
    have hσ : σ (τ g') = hex'.choose.1 := dif_pos hex'
    have hsτ : τ hex'.choose = τ g' := hex'.choose_spec
    set s' := hex'.choose with hs'
    refine ⟨s'.1, Finset.mem_image.2 ⟨τ g', Fintype.mem_piFinset.2 fun i => hτT g' i, hσ⟩, s'.2.1, s'.2.2,
      s'.1⁻¹ * g, ?_, ?_⟩
    · refine isKM_inv_mul hg s'.2.1 s'.2.2 ?_
      refine cong_of_gens hLo e he g s'.1 (into g hg) (into s'.1 s'.2.1) fun i => ?_
      refine ⟨yy g' i - yy s' i, sub_mem (hyy g' i) (hyy s' i), ?_⟩
      have h1 := hτ g' i
      have h2 := hτ s' i
      rw [hsτ] at h2
      change g *ᵥ fv _ (e i) = _ at h1
      rw [h1, h2, smul_sub]
      abel
    · rw [← mul_assoc, Matrix.mul_nonsing_inv _ (by rw [s'.2.2]; exact isUnit_one), one_mul]

end GlobalTheory.UCls.IdxK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceOfFiniteEtaleDegree
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TrDeg

open GlobalTheory.EtC.Tr

variable (R : Type) [CommRing R]

theorem chainMap_comp {X Y Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Y) (t' : freeSch R Y ⟶ freeSch R Z) :
    chainMap R (t ≫ t') = chainMap R t ≫ chainMap R t' := by
  have : simpMap R (t ≫ t') = simpMap R t ≫ simpMap R t' := by ext; rfl
  rw [chainMap, this, Functor.map_comp]
  exact CategoryTheory.Functor.map_comp _ _ _

theorem chainMap_add {X Y : Scheme.{0}} (t t' : freeSch R X ⟶ freeSch R Y) :
    chainMap R (t + t') = chainMap R t + chainMap R t' := by
  have : simpMap R (t + t') = simpMap R t + simpMap R t' := by ext; rfl
  rw [chainMap, this, Functor.map_add]
  exact (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map_add

theorem chainMap_zero {X Y : Scheme.{0}} : chainMap R (0 : freeSch R X ⟶ freeSch R Y) = 0 := by
  have h := chainMap_add R (0 : freeSch R X ⟶ freeSch R Y) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem along_comp {X Y Z : Scheme.{0}} (F : Shv R) (n : ℤ) (t : freeSch R X ⟶ freeSch R Y) (t' : freeSch R Y ⟶ freeSch R Z)
    (x : H R (sch.obj Z) F n) : along R F n (t ≫ t') x = along R F n t (along R F n t' x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, chainMap_comp, Cochain.ofHom_comp]

theorem along_add {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) (t t' : freeSch R X ⟶ freeSch R Y)
    (x : H R (sch.obj Y) F n) : along R F n (t + t') x = along R F n t x + along R F n t' x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine (congrArg CohomologyClass.mk (Cocycle.ext ?_)).trans (CohomologyClass.mk_add _ _)
  simp [zcomp, chainMap_add, Cochain.ofHom_add, Cochain.add_comp]

theorem along_nsmul_id (X : Scheme.{0}) (F : Shv R) (n : ℤ) (d : ℕ) (x : H R (sch.obj X) F n) :
    along R F n (d • 𝟙 (freeSch R X)) x = d • x := by
  induction d with
  | zero =>
    have h := along_add R F n (0 : freeSch R X ⟶ freeSch R X) 0 x
    rw [add_zero] at h
    rw [zero_smul, zero_smul]
    exact left_eq_add.1 h
  | succ d ih => rw [succ_nsmul, succ_nsmul, along_add, ih, along_id]

theorem generate_singleton_mem {U X : Scheme.{0}} (u : U ⟶ X) [Etale u] [Surjective u] :
    Sieve.generate (Presieve.singleton u) ∈ Scheme.etaleTopology X :=
  Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff (P := @Etale) u).2 ⟨(inferInstance : Surjective u).surj, inferInstance⟩)

theorem transfer_comp {Y X U : Scheme.{0}} {f : Y ⟶ X} {u : U ⟶ X} [Etale u] [Surjective u] {d : ℕ}
    {s : Fin d → (U ⟶ Y)} (hs : SplitBy f u s) {t : freeSch R X ⟶ freeSch R Y} (ht : IsTransfer R f t) :
    t ≫ (free R).map (yoneda.map f) = d • 𝟙 _ := by
  refine free_hom_ext_of_covering R _ _ _ _ (generate_singleton_mem u) ?_
  rintro V v ⟨_, g, _, ⟨⟩, rfl⟩
  have hg := splitBy_baseChange hs g
  rw [← Category.assoc, ht.apply_of_splitBy R hg, Preadditive.sum_comp]
  have h1 : ∀ j, (free R).map (yoneda.map (g ≫ s j)) ≫ (free R).map (yoneda.map f) =
      (free R).map (yoneda.map (g ≫ u)) := fun j => by
    rw [← Functor.map_comp, ← Functor.map_comp, hg.1 j]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Preadditive.comp_nsmul, Category.comp_id]

theorem splitBy_of_iso {Y X U : Scheme.{0}} (f : Y ⟶ X) (u : U ⟶ X) {d : ℕ}
    (e : ∐ (fun _ : Fin d => U) ≅ pullback f u) (he : e.hom ≫ pullback.snd f u = Limits.Sigma.desc (fun _ => 𝟙 U)) :
    SplitBy f u (fun j => Sigma.ι (fun _ : Fin d => U) j ≫ e.hom ≫ pullback.fst f u) := by
  have h1 : ∀ j, Sigma.ι (fun _ : Fin d => U) j ≫ e.hom ≫ pullback.snd f u = 𝟙 U := fun j => by
    rw [he, Sigma.ι_desc]
  have hs : ∀ j, (Sigma.ι (fun _ : Fin d => U) j ≫ e.hom ≫ pullback.fst f u) ≫ f = u := fun j => by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% (h1 j)]
  refine ⟨hs, ?_⟩
  convert (inferInstance : IsIso e.hom)
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_desc]
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc]
  · rw [pullback.lift_snd, Category.assoc, h1]

theorem trH_pull {Y X U : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] {u : U ⟶ X} [Etale u] [Surjective u] {d : ℕ}
    {s : Fin d → (U ⟶ Y)} (hs : SplitBy f u s) (F : Shv R) (n : ℤ) (x : H R (sch.obj X) F n) :
    trH R f F n (pull R (sch.map f) F n x) = d • x := by
  rw [trH, ← along_free, ← along_comp,
    transfer_comp R hs (transfer_spec R (existsUnique_isTransfer R f).exists), along_nsmul_id]

theorem exists_trace_pullHl : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] (d : ℕ), (∃ (U : Scheme.{0}) (u : U ⟶ X), Etale u ∧ Surjective u ∧ ∃ e : ∐ (fun _ : Fin d => U) ≅ pullback f u, e.hom ≫ pullback.snd f u = Limits.Sigma.desc (fun _ => 𝟙 U)) →
    ∀ n i : ℤ, ∃ tr : Hl l (sch.obj Y) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i, ∀ x, tr (pullHl l (sch.map f) n i x) = d • x := by
  rintro l _ Y X f _ _ d ⟨U, u, _, _, e, he⟩ n i
  refine ⟨trHl l f n i, fun x => Subtype.ext (funext fun k => ?_)⟩
  have h := trHl_spec l (redCompat_of_finite_etale l f (fun R _ => existsUnique_isTransfer R f) n i)
  exact (h _ k).trans (trH_pull (ZMod (l ^ k)) f (splitBy_of_iso f u e he) (tw (l ^ k) i) n (x.1 k))

end GlobalTheory.EtC.TrDeg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_cover_chart_smooth_normal : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ I : Finset (Fin (d + 1)), I.Nonempty → Module.Finite (rA k x I) (integralClosure (rA k x I) K) ∧ IsFractionRing (rB k K x I) K ∧ Algebra.Smooth k (rB k K x I) := by
  first | (exact @GlobalTheory.PD.rB_finite_frac_smooth) | (exact GlobalTheory.PD.rB_finite_frac_smooth) | (intros; apply GlobalTheory.PD.rB_finite_frac_smooth  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLaRingOfIntegersStatement
section
open NumberField GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_La_ringOfIntegers' : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p), letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O); Module.finrank (𝓞 D.F) D.La = D.m * D.n := by
  first | (exact @GlobalTheory.UPel.HT.Datum.finrank_La_ringOfIntegers) | (exact GlobalTheory.UPel.HT.Datum.finrank_La_ringOfIntegers) | (intros; apply GlobalTheory.UPel.HT.Datum.finrank_La_ringOfIntegers <;> assumption)
end

