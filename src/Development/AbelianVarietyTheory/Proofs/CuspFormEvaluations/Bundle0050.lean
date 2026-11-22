import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0047
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0048
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FullLinearLevelCoverBaseChangeTorsor
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mem_iff_modN (k : ℕ) (x : Dw.La) :
    x ∈ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La) ↔ Dw.ModN k x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨b, _, hb⟩ => ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩,
    fun ⟨b, hb⟩ => ⟨b, trivial, by rw [hb, Nat.cast_smul_eq_nsmul]⟩⟩

theorem mk_eq_iff (k : ℕ) (a b : Dw.La) :
    (Submodule.Quotient.mk a : LatMod Dw k) = Submodule.Quotient.mk b ↔ Dw.ModN k (a - b) := by
  rw [Submodule.Quotient.eq, mem_iff_modN]

theorem finite_latMod (k : ℕ) (hk : 0 < k) : Finite (LatMod Dw k) := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient Dw k hk
  refine Finite.of_surjective (fun j => (Submodule.Quotient.mk (r j) : LatMod Dw k)) fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨π a, (mk_eq_iff k _ _).2 ((hπ _ _).1 (hr _))⟩

theorem nsmul_latMod (k : ℕ) (q : LatMod Dw k) : k • q = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_iff_modN]
  exact ⟨a, Nat.cast_smul_eq_nsmul _ _ _⟩

variable (Xo : Moduli Dw l)

theorem exists_descend (k : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (ev : Dw.La → (ptO Xo x0 ⟶ Xo.univ.t.G)) (hadd : ∀ a b, ev (a + b) = ev a * ev b)
    (hlin : ∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) (hker : ∀ a, ev (k • a) = 1)
    (hinj : ∀ (K : Type) [Field K] (χ : S →+* K) (a b : Dw.La),
      spMap χ ≫ (ev a).left = spMap χ ≫ (ev b).left → Dw.ModN k (a - b)) :
    ∃ ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G), IsFullLev Xo k x0 ev' ∧
      ∀ a, ev' (Submodule.Quotient.mk a) = ev a := by
  choose r hr using Submodule.Quotient.mk_surjective (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La)
  have h : ∀ a, ev (r (Submodule.Quotient.mk a)) = ev a := fun a => by
    obtain ⟨b, hb⟩ := (mk_eq_iff k _ _).1 (hr (Submodule.Quotient.mk a))
    rw [sub_eq_iff_eq_add.1 hb, hadd, hker, _root_.one_mul]
  refine ⟨fun q => ev (r q), ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => ?_⟩, h⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    beta_reduce
    rw [← Submodule.Quotient.mk_add, h, h, h, hadd]
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    beta_reduce
    rw [← Submodule.Quotient.mk_smul, h, h, hlin]
  · rw [← hr a, ← hr b]
    exact (mk_eq_iff k _ _).2 (hinj K χ _ _ hab)

theorem pow_eq_one {k : ℕ} {S : Type} [CommRing S] {x0 : Sp S ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (h : IsFullLev Xo k x0 ev) (q : LatMod Dw k) : ev q ^ k = 1 := by
  let f : LatMod Dw k →+ Additive (ptO Xo x0 ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun q => Additive.ofMul (ev q)) fun a b => congrArg Additive.ofMul (h.1 a b)
  have := map_nsmul f k q
  rw [nsmul_latMod, map_zero] at this
  exact (congrArg Additive.toMul this).symm

theorem baseChange {k : ℕ} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x0 : Sp S ⟶ Xo.X}
    {x1 : Sp T ⟶ Xo.X} (h : ptO Xo x1 ⟶ ptO Xo x0) (hh : h.left = spMap ψ)
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) :
    IsFullLev Xo k x1 (fun q => h ≫ ev q) := by
  refine ⟨fun a b => ?_, fun o a => ?_, fun K _ χ a b hab => hev.2.2 K (χ.comp ψ) a b ?_⟩
  · beta_reduce
    rw [hev.1, MonObj.comp_mul]
  · beta_reduce
    rw [hev.2.1, Category.assoc]
  · have : spMap χ ≫ h.left ≫ (ev a).left = spMap χ ≫ h.left ≫ (ev b).left := hab
    rw [hh] at this
    rw [spMap_comp, Category.assoc, Category.assoc]
    exact this

theorem eq_of_agree (hL : Laws) {k : ℕ} (hk : 0 < k) {S T : Type} [CommRing S] [CommRing T] (χ : S →+* T)
    (hχ : ∀ e, χ e = 1 → IsUnit e) {x0 : Sp S ⟶ Xo.X} {a b : ptO Xo x0 ⟶ Xo.univ.t.G} (ha : a ^ k = 1)
    (hb : b ^ k = 1) (hab : spMap χ ≫ a.left = spMap χ ≫ b.left) : a = b := by
  obtain ⟨e, he, He⟩ := exists_isIdempotentElem_torsion_eq hL E H Dw l Xo S x0 k hk a b ha hb
  have h1 : e = 1 := (hχ e ((He T χ).2 hab)).mul_left_cancel (he.eq.trans (_root_.mul_one _).symm)
  have h2 := (He S (RingHom.id S)).1 h1
  have h3 : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id (CommRingCat.of S)
  rw [h3] at h2
  exact Over.OverMorphism.ext ((Category.id_comp _).symm.trans (h2.trans (Category.id_comp _)))

theorem exists_geometric (hL : Laws) {k : ℕ} (hk : 0 < k) (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X) :
    ∃ ev, IsFullLev Xo k x0 ev ∧ ∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x0 ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x0 β.hom hβ.symm
  obtain ⟨ev, hev, h⟩ := exists_descend Xo k x0 (I.ev k) (I.add k) (I.lin k) (fun a => (I.ker k hk _).2 ⟨a, rfl⟩)
    fun K' _ χ a b hab => by
      have h1 : I.ev k a = I.ev k b :=
        eq_of_agree Xo hL hk χ (fun e he => isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at he)
          ((I.onto k hk _).2 ⟨_, rfl⟩) ((I.onto k hk _).2 ⟨_, rfl⟩) hab
      have h2 : I.ev k a = I.ev k (a - b) * I.ev k b := by rw [← I.add, sub_add_cancel]
      rw [h2, mul_eq_right, I.ker k hk] at h1
      exact h1
  refine ⟨ev, hev, fun p hp => ?_⟩
  obtain ⟨a, ha⟩ := (I.onto k hk p).1 hp
  exact ⟨_, (h a).trans ha⟩

theorem onto_of_local (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (p : ptO Xo x0 ⟶ Xo.univ.t.G)
    (hp : p ^ k = 1) : ∃ q, ev q = p := by
  haveI := finite_latMod (Dw := Dw) k hk
  let K := AlgebraicClosure (IsLocalRing.ResidueField T)
  let χ : T →+* K := (algebraMap (IsLocalRing.ResidueField T) K).comp (IsLocalRing.residue T)
  have hχ : ∀ e, χ e = 1 → IsUnit e := fun e he => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    simp [χ, h0] at he
  let h : ptO Xo (spMap χ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap χ) rfl
  obtain ⟨ev₀, -, h₀⟩ := exists_geometric Xo hL hk K (spMap χ ≫ x0)
  have hpow : ∀ a : ptO Xo x0 ⟶ Xo.univ.t.G, a ^ k = 1 → (h ≫ a) ^ k = 1 := fun a ha => by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  choose f hf using fun q => h₀ (h ≫ ev q) (hpow _ (pow_eq_one Xo hev q))
  have hinj : Function.Injective f := fun a b hab => hev.2.2 K χ a b
    (congrArg CommaMorphism.left ((hf a).symm.trans ((congrArg ev₀ hab).trans (hf b))))
  obtain ⟨r, hr⟩ := h₀ (h ≫ p) (hpow p hp)
  obtain ⟨q, rfl⟩ := Finite.surjective_of_injective hinj r
  exact ⟨q, eq_of_agree Xo hL hk χ hχ (pow_eq_one Xo hev q) hp
    (congrArg CommaMorphism.left ((hf q).symm.trans hr))⟩

theorem injective_of_local {k : ℕ} {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) : Function.Injective ev :=
  fun a b hab => hev.2.2 _ (IsLocalRing.residue T) a b (by rw [hab])

theorem exists_levGrp (hL : Laws) {k : ℕ} (hk : 0 < k) {T : Type} [CommRing T] [IsLocalRing T] {x0 : Sp T ⟶ Xo.X}
    {ev ev' : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)} (hev : IsFullLev Xo k x0 ev) (hev' : IsFullLev Xo k x0 ev') :
    ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q) := by
  haveI := finite_latMod (Dw := Dw) k hk
  choose f hf using fun q => onto_of_local Xo hL hk hev (ev' q) (pow_eq_one Xo hev' q)
  have hi := injective_of_local Xo hev
  let g : LatMod Dw k →ₗ[𝓞 E] LatMod Dw k :=
    { toFun := f
      map_add' := fun a b => hi (by rw [hev.1, hf, hf, hf, hev'.1])
      map_smul' := fun o a => hi (by rw [RingHom.id_apply, hev.2.1, hf, hf, hev'.2.1]) }
  have hg : Function.Injective g := fun a b hab => injective_of_local Xo hev'
    ((hf a).symm.trans ((congrArg ev hab).trans (hf b)))
  exact ⟨LinearEquiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, fun q => (hf q).symm⟩

end FullLevel

open FullLevel in

theorem fullLevel_cover_baseChange_torsor :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : ℕ), 0 < k → (∀ (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X), ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (ev : LatMod Dw k → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ IsFullLev Xo k (spMap φ ≫ x0) ev) ∧ (∀ (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x0 : Sp S ⟶ Xo.X) (x1 : Sp T ⟶ Xo.X) (h : ptO Xo x1 ⟶ ptO Xo x0), h.left = spMap ψ → ∀ ev, IsFullLev Xo k x0 ev → IsFullLev Xo k x1 (fun q => h ≫ ev q) ∧ ∀ q, ev q ^ k = 1) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)), IsFullLev Xo k x0 ev → (∀ p : ptO Xo x0 ⟶ Xo.univ.t.G, p ^ k = 1 → ∃ q, ev q = p) ∧ ∀ ev', IsFullLev Xo k x0 ev' → ∃ g : LevGrp Dw k, ∀ q, ev' q = ev (g q)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x0 : Sp K ⟶ Xo.X), ∃ ev, IsFullLev Xo k x0 ev := by
  intro hL E _ _ _ H Dw l Xo k hk
  refine ⟨fun S _ x0 => ?_, fun S T _ _ ψ x0 x1 h hh ev hev => ⟨baseChange Xo ψ h hh hev, pow_eq_one Xo hev⟩,
    fun T _ _ x0 ev hev => ⟨onto_of_local Xo hL hk hev, fun ev' hev' => exists_levGrp Xo hL hk hev hev'⟩,
    fun K _ _ x0 => (exists_geometric Xo hL hk K x0).imp fun _ h => h.1⟩
  obtain ⟨B, _, φ, ev, hφ, h1, h2, h3, h4⟩ := exists_faithfullyFlat_linear_level hL E H Dw l Xo S x0 k hk
  obtain ⟨ev', hev', -⟩ := exists_descend Xo k _ ev h1 h2 h3 h4
  exact ⟨B, inferInstance, φ, ev', hφ, hev'⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsIntegralCoeffCof
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

noncomputable section

namespace GlobalTheory.FrameRead.CoefMap

def harmSub {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Submodule k (MvPolynomial (Letter T r n) k) where
  carrier := HHa r n k cc isX a
  add_mem' := by
    rintro P Q ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨add_mem h1 h1', fun σ i i' h t => by rw [map_add, h2 σ i i' h t, h2' σ i i' h t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact h3 m h
    · exact h3' m h
  zero_mem' := ⟨zero_mem _, fun σ i i' _ t => map_zero _, fun m hm => by simp at hm⟩
  smul_mem' := by
    rintro x P ⟨h1, h2, h3⟩
    exact ⟨Submodule.smul_mem _ x h1, fun σ i i' h t => by rw [map_smul, h2 σ i i' h t],
      fun m hm => h3 m (support_smul hm)⟩

theorem det_gen_ne_zero (K : Type) [Field K] {Ix : Type} (n : ℕ) (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)).mapMatrix (gen K n t) = 1 := by
    ext p q
    simp [gen, Matrix.one_apply]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem map_gen {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {Ix : Type} (n : ℕ) (t : Ix) :
    (MvPolynomial.map f).mapMatrix (gen R n t) = gen S n t := by
  ext p q : 2
  simp [gen]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {n : ℕ}
  {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))

theorem detFac_ne_zero (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    detFac Dw pl K a s lam ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (det_gen_ne_zero K n t)

theorem map_cof {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (Q : MvPolynomial (LtN Dw n) R) :
    MvPolynomial.map f (cof Dw pl R n Q) = cof Dw pl S n (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C x => simp [algHom_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ℓ hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [cof, aeval_X]
    split_ifs with h1 h2 h3
    · simp [gen]
    · rw [← map_gen f, ← RingHom.map_adjugate]
      rfl
    · simp
    · simp

theorem isIntegral_coeff_cof {K : Type} [Field K] (P : MvPolynomial (LtN Dw n) K)
    (hP : ∀ m, P.coeff m ∈ (integralClosure ℤ K).toSubring) (m) : IsIntegral ℤ ((cof Dw pl K n P).coeff m) := by
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.map (integralClosure ℤ K).toSubring.subtype Q = P := by
    refine ⟨∑ m ∈ P.support, monomial m ⟨P.coeff m, hP m⟩, ?_⟩
    simp only [map_sum, map_monomial, Subring.subtype_apply]
    exact P.as_sum.symm
  rw [← map_cof, coeff_map]
  exact ((cof Dw pl _ n Q).coeff m).2

set_option maxHeartbeats 1000000 in

theorem exists_ioLFRec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → ∃ (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam), IoLFRec c (fun t => embF c (pl t)) lam a io hw := by
  intro E _ _ _ H Dw n Ix _ pl he hn l c a s lam ha hwt
  obtain ⟨ε, hε⟩ := GlobalTheory.T.frameReading_leadingMinorProduct_extremal E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨him, hex, heq⟩ := GlobalTheory.T.hodge_weight_dominance_condition E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨hpG, -, -⟩ := pG_mem_ne_zero_generates E H Dw n Ix pl he hn l c a ha
  obtain ⟨-, -, hstab⟩ := letAct_mul_one_mem_HHa E H Dw n Ix pl he hn c.F a
  obtain ⟨hs1, hs2, hs3⟩ := GlobalTheory.StdNab.nabAtr_stdLat E c.F Ix n (fun t => embF c (pl t)) lam
  have hD := detFac_ne_zero Dw pl c.F a s lam
  let S := harmSub Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
  have hS : ∀ P, P ∈ S ↔ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) :=
    fun _ => Iff.rfl
  set e : c.F := ((ε : ℤ) : c.F) with he'
  have hee : e * e = 1 := by
    rw [he', ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have heI : IsIntegral ℤ e := isIntegral_intCast _
  set D := detFac Dw pl c.F a s lam with hDdef
  have hex' : ∀ F : VVc c lam, ∃! P, P ∈ S ∧ cof Dw pl c.F n P = e • (D * F.1) := fun F => by
    have := hex (e • F.1) (Submodule.smul_mem _ _ F.2)
    rwa [mul_smul_comm] at this
  choose φ hφ huniq using hex'
  have hu : ∀ (F : VVc c lam) P, P ∈ S → cof Dw pl c.F n P = e • (D * F.1) → φ F = P :=
    fun F P h1 h2 => (huniq F P ⟨h1, h2⟩).symm
  let io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F :=
    { toFun := φ
      map_add' := fun F G => hu _ _ (add_mem (hφ F).1 (hφ G).1) (by
        rw [map_add, (hφ F).2, (hφ G).2, Submodule.coe_add, mul_add, smul_add])
      map_smul' := fun x F => hu _ _ (Submodule.smul_mem _ _ (hφ F).1) (by
        rw [map_smul, (hφ F).2, Submodule.coe_smul, mul_smul_comm, smul_comm]; rfl) }
  have hio : ∀ F, io F = φ F := fun _ => rfl
  have hsurj : ∀ P ∈ S, ∃ F : VVc c lam, io F = P := fun P hP => by
    obtain ⟨F, hF, h⟩ := him P hP
    refine ⟨⟨e • F, Submodule.smul_mem _ _ hF⟩, hu _ _ hP ?_⟩
    rw [h, mul_smul_comm, smul_smul, hee, one_smul]
  have hwm : (ten fun t => extremal c.F n (lam t)) ∈ VV c.F lam := by
    obtain ⟨F, hF, h⟩ := him _ hpG.1
    rw [hε, ← mul_smul_comm] at h
    have h' := mul_left_cancel₀ hD h
    have : (ten fun t => extremal c.F n (lam t)) = e • F := by rw [← h', smul_smul, hee, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hF
  refine ⟨io, ⟨_, hwm⟩, rfl, fun ga => if h : IsUnit ga.det then
      ∏ t, (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h))) t : GL (Fin n) c.F) :
        Matrix (Fin n) (Fin n) c.F).det ^ (s t) else 0, hn, ?_, ?_, ?_, (hs1 _).2 hs2,
      fun x hx => hs3 x ((hs1 _).1 hx), hu _ _ hpG.1 hε, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro F hF
    have h := (hφ F).2
    rw [← hio, hF, map_zero] at h
    have h' := congrArg (fun x => e • x) h
    simp only [smul_zero, smul_smul, hee, one_smul] at h'
    exact Subtype.ext ((mul_eq_zero.1 h'.symm).resolve_left hD)
  · have : Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) = S :=
      Submodule.span_eq S
    rw [this]
    refine le_antisymm ?_ hsurj
    rintro _ ⟨F, rfl⟩
    exact (hφ F).1
  · intro ga hga F
    have h : IsUnit ga.det := by
      have := congrArg Matrix.det hga
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact IsUnit.of_mul_eq_one_right _ this
    rw [gaStar_conj_eq_letAct E H Dw n Ix pl he hn l c ga h hga]
    simp only [dif_pos h, rhoM]
    set g := invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) with hg
    refine hu _ _ (Submodule.smul_mem _ _ (hstab g _ (hφ F).1)) ?_
    have h1 := heq g _ (hφ F).1 (e • F.1) (Submodule.smul_mem _ _ F.2) (by rw [(hφ F).2, mul_smul_comm])
    rw [map_smul, hio, h1, smul_smul, ← Finset.prod_mul_distrib, map_smul, mul_smul_comm]
    have h2 : ∏ t, (g t : Matrix (Fin n) (Fin n) c.F).det ^ (s t) * (g t : Matrix (Fin n) (Fin n) c.F).det ^ (-(s t)) = 1 :=
      Finset.prod_eq_one fun t _ => by
        rw [← zpow_add₀ (Matrix.isUnits_det_units (g t)).ne_zero, add_neg_cancel, zpow_zero]
    rw [h2, one_smul]
    rfl
  · intro P hP
    obtain ⟨F, rfl⟩ := hsurj P hP.1
    refine ⟨F, (hs1 F).2 (GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral c.F Ix n lam
      (fun t => ((degC Dw pl a t : ℤ) + (lam t).detShift - s t).toNat) F.1 F.2 fun m => ?_), rfl⟩
    have h : e • cof Dw pl c.F n (φ F) = D * F.1 := by rw [(hφ F).2, smul_smul, hee, one_smul]
    change IsIntegral ℤ ((D * F.1).coeff m)
    rw [← h, coeff_smul, smul_eq_mul]
    exact heI.mul (isIntegral_coeff_cof Dw pl (φ F) hP.2 m)

end GlobalTheory.FrameRead.CoefMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem thExpr_tmul_lemma (hL : Laws) (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    [StarRing (𝓞 E)] {nab : NabV Xo c} (hnab : IsNab Xo c nab) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (x : Fin n → Dw.La)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n)
    {S1 : Type} [CommRing S1] [Algebra c.F S1] [Algebra S S1] (φ1 : S →ₐ[c.F] S1)
    (hφ1 : ∀ s, φ1 s = algebraMap S S1 s) (y1 : FrPt Xo c S1)
    (F1 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y1.x)))
    (h1 : FrMap φ1 y y1)
    (hF1 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y1.s
      (levPt Xo y1.x (x b)) (F1 b))
    {S2 : Type} [CommRing S2] [Algebra c.F S2] [Algebra S S2] (φ2 : S →ₐ[c.F] S2)
    (hφ2 : ∀ s, φ2 s = algebraMap S S2 s) (y2 : FrPt Xo c S2)
    (F2 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y2.x)))
    (h2 : FrMap φ2 y y2)
    (hF2 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y2.s
      (levPt Xo y2.x (x b)) (F2 b)) :
    TensorProduct.tmul S (thExpr Xo c nab y1 P F1) (1 : S2) =
      TensorProduct.tmul S (1 : S1) (thExpr Xo c nab y2 P F2) := by
  letI : Algebra c.F (TensorProduct S S1 S2) :=
    ((algebraMap S (TensorProduct S S1 S2)).comp (algebraMap c.F S)).toAlgebra
  let χ1 : S1 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeLeft
  let χ2 : S2 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeRight

  let ψ1 : S1 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ1.toRingHom with
      commutes' := fun r => by
        show χ1 (algebraMap c.F S1 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ1.commutes r, hφ1]
        exact χ1.commutes _ }
  let ψ2 : S2 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ2.toRingHom with
      commutes' := fun r => by
        show χ2 (algebraMap c.F S2 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ2.commutes r, hφ2]
        exact χ2.commutes _ }
  have hcomp : ψ1.comp φ1 = ψ2.comp φ2 := by
    ext s
    show χ1 (φ1 s) = χ2 (φ2 s)
    rw [hφ1, hφ2, χ1.commutes, χ2.commutes]
  exact GlobalTheory.T.thetaExpression_eq_of_witnesses hL hC E H Dw l Xo c nab hnab S y a n x P hP S1 φ1 y1 F1 S2 φ2 y2 F2 h1 hF1 h2 hF2
    (TensorProduct S S1 S2) ψ1 ψ2 hcomp

theorem thValTot_of_chartIndep : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y a n x P hP

  obtain ⟨S', _, _, φ, y', F, hff, hy', hF⟩ := GlobalTheory.T.exists_faithfullyFlat_cover_level_sections hL E H Dw l Xo c S y n x
  letI : Algebra S S' := φ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S' := hff
  have hφ : ∀ s, φ s = algebraMap S S' s := fun _ => rfl

  have htmul := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ hφ y' F hy' hF
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S S' (thExpr Xo c nab y' P F)).mp
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, htmul, sub_self])
  refine ⟨v, ⟨S', inferInstance, inferInstance, φ, y', F, hff, hy', hF, hv⟩, ?_⟩

  rintro w ⟨S2, _, _, φ2, y2, F2, hff2, hy2, hF2, hw⟩
  letI : Algebra S S2 := φ2.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S2 := hff2
  have h12 := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ2 (fun _ => rfl) y2 F2 hy2 hF2
  have hv' : φ v = thExpr Xo c nab y' P F := hv
  rw [← hv', ← hw, hφ, Algebra.TensorProduct.tmul_one_eq_one_tmul] at h12
  have h3 : algebraMap S S2 v = algebraMap S S2 w :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := S) (B := S') S2 h12
  exact (FaithfulSMul.algebraMap_injective S S2 h3).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem thetaValue_natural : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S T _ _ _ _ φ y0 y hφ a n x P hP v0 w h0 h1
  obtain ⟨S', _, _, φ0, y0', F0, hff0, hm0, hv0, he0⟩ := h0
  obtain ⟨T', _, _, φ1, y1, F1, hff1, hm1, hv1, he1⟩ := h1

  have hm01 : FrMap (φ1.comp φ) y0 y1 := GlobalTheory.FramedBaseChange.trans φ φ1 hφ hm1

  let iS : Algebra S S' := φ0.toRingHom.toAlgebra
  let iT : Algebra S T' := (φ1.comp φ).toRingHom.toAlgebra
  have : Module.FaithfullyFlat S S' := hff0
  let iU : Algebra c.F (TensorProduct S T' S') :=
    ((algebraMap T' (TensorProduct S T' S')).comp (algebraMap c.F T')).toAlgebra
  have hsq : ∀ s : S, (1 : T') ⊗ₜ[S] φ0 s = (φ1 (φ s)) ⊗ₜ[S] (1 : S') := by
    intro s
    calc (1 : T') ⊗ₜ[S] φ0 s = (1 : T') ⊗ₜ[S] (s • (1 : S')) := by
          rw [← Algebra.algebraMap_eq_smul_one]; rfl
      _ = (s • (1 : T')) ⊗ₜ[S] (1 : S') := (TensorProduct.smul_tmul _ _ _).symm
      _ = (φ1 (φ s)) ⊗ₜ[S] (1 : S') := by
          rw [← Algebra.algebraMap_eq_smul_one]; rfl
  let ψ2 : T' →ₐ[c.F] TensorProduct S T' S' :=
    { algebraMap T' (TensorProduct S T' S') with commutes' := fun _ => rfl }
  let ψ1 : S' →ₐ[c.F] TensorProduct S T' S' :=
    { (Algebra.TensorProduct.includeRight : S' →ₐ[S] TensorProduct S T' S').toRingHom with
      commutes' := fun r => by
        show (1 : T') ⊗ₜ[S] algebraMap c.F S' r = algebraMap T' (TensorProduct S T' S') (algebraMap c.F T' r)
        rw [← φ0.commutes r, hsq, φ.commutes, φ1.commutes]
        rfl }
  have hcomp : ψ1.comp φ0 = ψ2.comp (φ1.comp φ) := by
    ext s
    exact hsq s
  have key := GlobalTheory.T.thetaExpression_eq_of_witnesses hL hC E H Dw l Xo c nab hnab S y0 a n x P hP S' φ0 y0' F0 T' (φ1.comp φ)
    y1 F1 hm0 hv0 hm01 hv1 (TensorProduct S T' S') ψ1 ψ2 hcomp
  rw [← he0, ← he1] at key
  have hv : ψ1 (φ0 v0) = ψ2 (φ1 (φ v0)) := congrArg (fun f => f v0) hcomp
  have hinj : Function.Injective (algebraMap T' (TensorProduct S T' S')) :=
    FaithfulSMul.algebraMap_injective T' (TensorProduct S T' S')
  exact hff1.injective (hinj (hv.symm.trans key))

end GlobalTheory
end

