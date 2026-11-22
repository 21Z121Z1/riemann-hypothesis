import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0062
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingLinearHomSpanGramForm
section
set_option autoImplicit false

noncomputable section

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

section Calc

variable {S : Scheme.{0}} {X Y A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj C] [IsCommMonObj C] {L : LB A.left} {M : LB B.left} {N : LB C.left}

theorem lamEq_symm' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq M g₁ g₂ L f₁ f₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).1

theorem lamEq_swap' (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) : LamEq L f₂ f₁ M g₂ g₁ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.1

theorem lamEq_trans' (hL : L.IsLB) (hM : M.IsLB) (hN : N.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B}
    {g₂ : Y ⟶ B} {k₁ : X ⟶ C} {k₂ : Y ⟶ C} (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq M g₁ g₂ N k₁ k₂) :
    LamEq L f₁ f₂ N k₁ k₂ :=
  ((LamCalc.lamEq_calculus S X Y A B C L M N hL hM hN f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ k₁ k₂).2.1 h).2.2.1 h'

theorem lamEq_pre (hL : L.IsLB) (hM : M.IsLB) {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) {X' Y' : Over S} (a : X' ⟶ X) (b : Y' ⟶ Y) :
    LamEq L (a ≫ f₁) (b ≫ f₂) M (a ≫ g₁) (b ≫ g₂) :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ f₂ f₂ g₁ g₁ g₂ g₂ g₁ g₂).2.1 h).2.2.2.1 X' Y' a b

variable (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen)
include hL hM hT hT'

theorem lamEq_mul_left' {f₁ f₁' : X ⟶ A} {f₂ : Y ⟶ A} {g₁ g₁' : X ⟶ B} {g₂ : Y ⟶ B}
    (h : LamEq L f₁ f₂ M g₁ g₂) (h' : LamEq L f₁' f₂ M g₁' g₂) : LamEq L (f₁ * f₁') f₂ M (g₁ * g₁') g₂ :=
  ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁' f₂ f₂ g₁ g₁' g₂ g₂ g₁ g₂).2.2.1 hT hT' h).1 h'

theorem lamEq_prod_left {J : Type} (s : Finset J) (f : J → (X ⟶ A)) (g : J → (X ⟶ B)) (f₂ : Y ⟶ A) (g₂ : Y ⟶ B)
    (h0 : LamEq L (1 : X ⟶ A) f₂ M (1 : X ⟶ B) g₂) (h : ∀ i ∈ s, LamEq L (f i) f₂ M (g i) g₂) :
    LamEq L (s.prod f) f₂ M (s.prod g) g₂ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM (f i) (s.prod f) f₂ f₂ (g i) (s.prod g) g₂ g₂
      (g i) g₂).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).1
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lamEq_prod_right {J : Type} (s : Finset J) (f₁ : X ⟶ A) (g₁ : X ⟶ B) (f : J → (Y ⟶ A)) (g : J → (Y ⟶ B))
    (h0 : LamEq L f₁ (1 : Y ⟶ A) M g₁ (1 : Y ⟶ B)) (h : ∀ i ∈ s, LamEq L f₁ (f i) M g₁ (g i)) :
    LamEq L f₁ (s.prod f) M g₁ (s.prod g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact ((LamCalc.lamEq_calculus S X Y A B B L M M hL hM hM f₁ f₁ (f i) (s.prod f) g₁ g₁ (g i) (s.prod g)
      g₁ (g i)).2.2.1 hT hT' (h i (Finset.mem_insert_self i s))).2
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Calc

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (act : OAct O G)

theorem act_zero' : act.act 0 = 1 := by
  have h := act.add 0 0
  rw [add_zero] at h
  have := congrArg (fun u => (act.act 0)⁻¹ * u) h
  simpa using this.symm

theorem act_sum' {J : Type} (s : Finset J) (c : J → O) : act.act (s.sum c) = s.prod fun i : J => act.act (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using act_zero' act
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, act.add, ih]

end Act

theorem exists_thetaGen' (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) :
    ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
  obtain ⟨ρ, hρ⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := hL.cube S P ⟨P.L, ρ, P.isLB, hρ⟩ rfl
  exact ⟨c.t, c.isGen⟩

theorem weilEq_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (m : ℕ), 0 < m → ∀ (z : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G),
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ (x : Fin p → 𝓞 E) (r : 𝓞 E), (m : 𝓞 E) * r = ∑ a, ∑ b, z a * gP a b * (H.bar (x b) : 𝓞 E) →
    GlobalTheory.CM.WeilEq X.B.t.PP.L f (∏ b, ((X.A true).t.act.act (x b) ≫ GlobalTheory.FlatCM.phiP X b))
      (X.A true).t.PP.L ((X.A true).t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X gP gQ hG m hm z f hf hfm x r hr
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  have hβ : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have lA : (X.A true).t.PP.L.IsLB := (X.A true).t.PP.isLB
  have lB : X.B.t.PP.L.IsLB := X.B.t.PP.isLB
  have tA := exists_thetaGen' hL (X.A true).pol
  have tB := exists_thetaGen' hL X.B.pol
  haveI : IsMonHom f := hf.1
  haveI hφ : ∀ a, IsMonHom (phiP X a) := fun a => (X.lin (Sum.inl a)).1
  haveI hact : ∀ s, IsMonHom ((X.A true).t.act.act s) := (X.A true).t.act.hom
  have toLam : ∀ (f₁ f₂ : (X.A true).t.G ⟶ X.B.t.G) (g₁ g₂ : (X.A true).t.G ⟶ (X.A true).t.G), IsMonHom f₁ →
      IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ →
      WeilEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
      LamEq X.B.t.PP.L f₁ f₂ (X.A true).t.PP.L g₁ g₂ := fun f₁ f₂ g₁ g₂ h₁ h₂ h₃ h₄ h =>
    (PairingFibre.lamEq_weilEq_over_ring hL (𝓞 K) (X.A true).pol (X.A true).pol X.B.pol (X.A true).pol f₁ f₂ g₁ g₂
      h₁ h₂ h₃ h₄ ℂ _).2 inferInstance hβ h

  have E1 : ∀ a b, LamEq X.B.t.PP.L ((X.A true).t.act.act (z a) ≫ phiP X a) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro a b
    have := lamEq_pre lB lA (toLam _ _ _ _ (hφ a) (hφ b) (hact _) inferInstance (hG.1 a b))
      ((X.A true).t.act.act (z a)) ((X.A true).t.act.act (x b))
    rwa [← (X.A true).t.act.mul, Category.comp_id] at this

  have S1 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b)
      (X.A true).t.PP.L ((X.A true).t.act.act (∑ a, z a * gP a b)) ((X.A true).t.act.act (x b)) := by
    intro b
    have h0 : LamEq X.B.t.PP.L (1 : (X.A true).t.G ⟶ X.B.t.G) ((X.A true).t.act.act (x b) ≫ phiP X b)
        (X.A true).t.PP.L (1 : (X.A true).t.G ⟶ (X.A true).t.G) ((X.A true).t.act.act (x b)) := by
      have := lamEq_pre lB lA (E1 b b) (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
    have := lamEq_prod_left lB lA tB tA Finset.univ (fun a => (X.A true).t.act.act (z a) ≫ phiP X a)
      (fun a => (X.A true).t.act.act (z a * gP a b)) _ _ h0 (fun a _ => E1 a b)
    rwa [← hfm, ← act_sum'] at this

  have M1 : ∀ t y : 𝓞 E, LamEq (X.A true).t.PP.L ((X.A true).t.act.act t) ((X.A true).t.act.act y)
      (X.A true).t.PP.L ((X.A true).t.act.act (t * H.bar y)) (𝟙 _) := by
    intro t y
    have h2 := lamEq_pre lA lA (lamEq_swap' lA lA (LamF.lamEq_adj (X.A true).t y)) ((X.A true).t.act.act t) (𝟙 _)
    rwa [Category.comp_id, Category.id_comp, Category.id_comp, ← (X.A true).t.act.mul] at h2
  have F2 : ∀ b, LamEq X.B.t.PP.L (f ^ m) ((X.A true).t.act.act (x b) ≫ phiP X b) (X.A true).t.PP.L (𝟙 _)
      ((X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) := fun b =>
    lamEq_trans' lB lA lA (lamEq_trans' lB lA lA (S1 b) (M1 _ _)) (LamF.lamEq_adj (X.A true).t _)

  obtain ⟨r', hr'⟩ := GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP f
    (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) hf (isLinearHom_prod X x)
  haveI hψ : IsMonHom (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) := (isLinearHom_prod X x).1
  have R := toLam _ _ _ _ inferInstance hψ (hact r') inferInstance hr'
  have Rm : ∀ n : ℕ, LamEq X.B.t.PP.L (f ^ n) (∏ b, ((X.A true).t.act.act (x b) ≫ phiP X b)) (X.A true).t.PP.L
      ((X.A true).t.act.act ((n : 𝓞 E) * r')) (𝟙 _) := by
    intro n
    induction n with
    | zero =>
      have := lamEq_pre lB lA R (1 : (X.A true).t.G ⟶ (X.A true).t.G) (𝟙 _)
      rw [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
      rwa [pow_zero, Nat.cast_zero, zero_mul, act_zero']
    | succ n ih =>
      rw [pow_succ, Nat.cast_succ, add_mul, _root_.one_mul, (X.A true).t.act.add]
      exact lamEq_mul_left' lB lA tB tA ih R
  have RmA := lamEq_trans' lB lA lA (Rm m) (LamF.lamEq_adj (X.A true).t ((m : 𝓞 E) * r'))
  have base2 : LamEq X.B.t.PP.L (f ^ m) (1 : (X.A true).t.G ⟶ X.B.t.G) (X.A true).t.PP.L (𝟙 _)
      (1 : (X.A true).t.G ⟶ (X.A true).t.G) := by
    have := lamEq_pre lB lA RmA (𝟙 _) (1 : (X.A true).t.G ⟶ (X.A true).t.G)
    rwa [MonObj.one_comp, MonObj.one_comp, Category.id_comp, Category.id_comp] at this
  have S2 := lamEq_prod_right lB lA tB tA Finset.univ (f ^ m) (𝟙 _)
    (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (X.A true).t.act.act (H.bar ((∑ a, z a * gP a b) * H.bar (x b)))) base2 (fun b _ => F2 b)
  have hsum : (∑ b, H.bar ((∑ a, z a * gP a b) * H.bar (x b))) = H.bar ((m : 𝓞 E) * r) := by
    rw [hr, ← map_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [← act_sum', hsum] at S2

  have U := lamEq_swap' lA lA (lamEq_trans' lA lB lA (lamEq_symm' lB lA S2) RmA)
  have e₁ := PairingInj.eq_of_lamEq hL _ (X.A true).pol _ _ _ U
  have hg : 1 ≤ (X.A true).pol.g := NumInh.dim_pos_of_hasType X.split X.ρ_sq (X.A true) X.typeP
  have e₂ := H.bar.injective (LamF.Faithful.act_injective hL E K (X.A true).pol (X.A true).t.act hg e₁)
  have e₃ : r = r' := mul_left_cancel₀ (Nat.cast_ne_zero.2 hm.ne' : (m : 𝓞 E) ≠ 0) e₂
  rw [e₃]
  exact hr'

end GlobalTheory.FlatCM.HomLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HeisSchA

open GlobalTheory.Published.Metaplectic
open scoped Classical

theorem nonarch_of_isInducing {G S : Type} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    [AddGroup S] [TopologicalSpace S] [IsTopologicalAddGroup S] (f : S →+ G) (hf : Topology.IsInducing f) :
    NonarchimedeanAddGroup S where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean t ht
    exact ⟨V.comap f hf.continuous, fun x hx => hsub (hV hx)⟩

theorem nonarch_pi {ι : Type} {G : ι → Type} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi I fun i => (K i : AddSubgroup (G i)), isOpen_set_pi hI fun i _ => (K i).isOpen⟩,
      fun x hx => hs fun i hi => hK i (hx i hi)⟩

variable {F : Type} [Field F] [NumberField F]

theorem nonarch_finiteAdeleRing : NonarchimedeanAddGroup (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), NonarchimedeanAddGroup (v.adicCompletionIntegers F) := fun v =>
    nonarch_of_isInducing (v.adicCompletionIntegers F).subtype.toAddMonoidHom Topology.IsInducing.subtypeVal
  haveI := nonarch_pi (G := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ FiniteAdeleRing (𝓞 F) F :=
    { toFun := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact NonarchimedeanAddGroup.nonarchimedean_of_emb f
    (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _))

def finChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem finChar_isLocallyConstant (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) :
    IsLocallyConstant (finChar ψ) := by
  haveI := nonarch_finiteAdeleRing (F := F)
  exact GlobalTheory.WeilM.isLocallyConstant_addChar _ (hψ.comp (continuous_const.prodMk continuous_id))

def p1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _

def p2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _

def mk (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (a, b)

theorem finChar_apply (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (z : FiniteAdeleRing (𝓞 F) F) :
    finChar ψ z = ψ (mk 0 z) := rfl

theorem map_eq_mul (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (b : AdeleRing (𝓞 F) F) :
    ψ b = ψ (mk (p1 b) 0) * finChar ψ (p2 b) := by
  rw [finChar_apply, ← AddChar.map_add_eq_mul]
  congr 1
  exact Prod.ext (add_zero _).symm (zero_add _).symm

theorem at_mk (b : InfiniteAdeleRing F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (mk b 0) := by
  intro u hu
  have hu1 : p1 u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  rw [smul_eq_mul]
  exact Prod.ext (show p1 u * b = 0 by rw [hu1, zero_mul]) (show p2 u * 0 = 0 from mul_zero _)

variable {κ : Type} [Fintype κ]

def trL (c : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem trL_apply (c y : κ → mixedEmbedding.mixedSpace F) :
    trL c y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c) := rfl

def archS (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (c t : κ → mixedEmbedding.mixedSpace F) (k : ℝ) :
    SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun y => eChar ((-trL c) y + -k)) (SchwartzMap.compSubConstCLM ℂ (-t) f)

theorem archS_apply (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (c t : κ → mixedEmbedding.mixedSpace F)
    (k : ℝ) (y : κ → mixedEmbedding.mixedSpace F) :
    archS f c t k y = eChar ((-trL c) y + -k) * f (y + t) := by
  have htg : Function.HasTemperateGrowth (fun y => eChar ((-trL c) y + -k)) :=
    hasTemperateGrowth_eChar.comp ((-trL c).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))
  rw [archS, SchwartzMap.smulLeftCLM_apply_apply htg, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul]

def finS (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (d s : κ → FiniteAdeleRing (𝓞 F) F) (d₀ : FiniteAdeleRing (𝓞 F) F) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun z => finChar ψ (z ⬝ᵥ d + d₀) * g (z + s)

theorem finS_mem (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (d s : κ → FiniteAdeleRing (𝓞 F) F)
    (d₀ : FiniteAdeleRing (𝓞 F) F) : finS ψ g d s d₀ ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have hlin : Continuous fun z : κ → FiniteAdeleRing (𝓞 F) F => z ⬝ᵥ d + d₀ :=
    (continuous_id.dotProduct continuous_const).add continuous_const
  refine ⟨((finChar_isLocallyConstant ψ hψ).comp_continuous hlin).mul
    (hg.1.comp_continuous (continuous_add_right s)), ?_⟩
  exact (hg.2.comp_homeomorph (Homeomorph.addRight s)).mul_left

theorem schr_pureA_mem [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.pureA F f g) ∈ GlobalTheory.WeilM.schA F κ := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  refine Submodule.subset_span ⟨archS f c t k, finS ψ g d s (p2 h), finS_mem ψ hψ.1 hg d s (p2 h), funext fun x => ?_⟩
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add, RingHom.map_dotProduct]
        rfl
      rw [e1, map_add, eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add, RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

theorem schr_mem_schA [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) :
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilM.schr ψ w Φ ∈ GlobalTheory.WeilM.schA F κ := by
  let T : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := GlobalTheory.WeilM.schr ψ w
      map_add' := fun φ φ' => funext fun x => by simp only [GlobalTheory.WeilM.schr, Pi.add_apply]; ring
      map_smul' := fun a φ => funext fun x => by
        simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.schA F κ).comap T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    exact schr_pureA_mem ψ hψ w f hg
  exact fun Φ hΦ => hle hΦ

end GlobalTheory.HeisSchA

theorem GlobalTheory.HeisSchA.rho_mem_schA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X Y)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
      M.co.rho ψ γ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
  fun M ψ hψ γ Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA ψ hψ (M.co.e γ) Φ hΦ
end
end

