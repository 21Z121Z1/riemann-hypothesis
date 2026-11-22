import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3446
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3447
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDataSizedFamilyStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_data_sized_family : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (X : GlobalTheory.Mem.Stages) (px : GlobalTheory.Mem.PreX X.B.toPre) (I : GlobalTheory.Mem.Col2.ColIn X.B px) (hX : X.B.fields.Ok) (Tw : GlobalTheory.Mem.Top.TwDat X.B) (Wt : Set X.B.places.Pl) (z : GlobalTheory.Mem.R3.Dat X I hX Tw Wt) (L : SizeData₂ X.toD7), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) → z.R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Holds z.R z.F := by
  first | exact @GlobalTheory.PrimIn.holds_of_ties | exact GlobalTheory.PrimIn.holds_of_ties | (intros; apply GlobalTheory.PrimIn.holds_of_ties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCechRelationDlogDescendsToAbelianPartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaud_cech_relation_dlog_descends_to_abelian_part : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (δH : Fld Y.H.left) (δ : Fld Q.P.A.left), (∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U → δH W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = dlg Y.H Y.q.left Q.P.L δH (jk k) (jk k') Wo) → ∃ (V : K → Q.P.A.left.Opens) (b : ∀ k, Γ(Q.P.A.left, V k)), ⨆ k, V k = ⊤ ∧ (∀ k, V k ≤ Q.P.L.U (jk k)) ∧ ∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg Q.P.A (𝟙 _) Q.P.L δ (jk k) (jk k') (V k ⊓ V k') := by
  first | exact @GlobalTheory.Heat.AbDescent.descent | exact GlobalTheory.Heat.AbDescent.descent | (intros; apply GlobalTheory.Heat.AbDescent.descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCoordinateConstantAdditiveInCharacter
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

theorem dlog_const_add {S S' : Type} [CommRing S] [CommRing S'] (π : S →+* S') (δ : S → S')
    (hδ : ∀ x y, δ (x * y) = π x * δ y + π y * δ x) (u₁ u₂ u₃ t : Sˣ) (hu : u₃ * t = u₁ * u₂)
    (k₁ k₂ k₃ : S') (h₁ : δ u₁ = π u₁ * k₁) (h₂ : δ u₂ = π u₂ * k₂) (h₃ : δ u₃ = π u₃ * k₃) (ht : δ t = 0) :
    k₃ = k₁ + k₂ := by
  have e := congrArg δ (congrArg Units.val hu)
  simp only [Units.val_mul, hδ, h₁, h₂, h₃, ht] at e
  have hπ := congrArg π (congrArg Units.val hu)
  simp only [Units.val_mul, map_mul] at hπ
  have hunit : IsUnit (π u₃ * π t) := by simpa only [Units.val_mul, map_mul] using (u₃ * t).isUnit.map π
  apply hunit.mul_left_cancel
  linear_combination e - (k₁ + k₂) * hπ

theorem coordEq_const_add : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ (α β : Q.X) (c₁ c₂ c₃ : K), CoordEq Y h ν m₀ V pb α c₁ → CoordEq Y h ν m₀ V pb β c₂ → CoordEq Y h ν m₀ V pb (α + β) c₃ → c₃ = c₁ + c₂ := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD hCm α β c₁ c₂ c₃ H₁ H₂ H₃
  obtain ⟨hd, hcov, hV, -⟩ := hC
  have P := hF.pull.1
  let z : Sp K := IsLocalRing.closedPoint K
  let a : Sp K ⟶ Y.H.left := spMap φ ≫ η[Y.H].left
  have hb : (spMap φ ≫ η[Q.P.A].left) ≫ Q.P.A.hom = 𝟙 (Sp K) ≫ spMap φ := by
    rw [Category.assoc, Over.w η[Q.P.A], Category.id_comp]
    rfl
  let b : Sp K ⟶ A₀.left := P.lift _ _ hb
  have hbm : b ≫ m₀ = spMap φ ≫ η[Q.P.A].left := P.lift_fst _ _ _
  have hbA : b ≫ A₀.hom = 𝟙 _ := P.lift_snd _ _ _
  have w : a ≫ Y.q.left = b ≫ m₀ := by
    have := Y.q_linear.isMonHom
    rw [hbm, Category.assoc, ← Over.comp_left, IsMonHom.one_hom]
  have hA3 : ∀ χ : Q.X, η[Q.P.A].left ≫ Q.famφB χ 3 = η[Q.P.A].left := fun χ => by
    change η[Q.P.A].left ≫ (toUnit Q.P.A ≫ η[Q.P.A]).left = _
    rw [← Over.comp_left, ← Category.assoc, toUnit_unique (η[Q.P.A] ≫ toUnit Q.P.A) (𝟙 _), Category.id_comp]
  have hA12 : ∀ χ : Q.X, η[Q.P.A].left ≫ Q.famφB χ 1 = η[Q.P.A].left ≫ Q.famφB χ 2 := fun χ => by
    change η[Q.P.A].left ≫ (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c χ)).left = η[Q.P.A].left ≫ (toUnit Q.P.A ≫ Q.c χ).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    change η[Q.P.A] ≫ (𝟙 Q.P.A * (toUnit _ ≫ Q.c χ)) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc η[Q.P.A] (toUnit _), toUnit_unique (η[Q.P.A] ≫ toUnit Q.P.A) (𝟙 _),
      Category.id_comp]
    have e1 : (η[Q.P.A] : 𝟙_ _ ⟶ Q.P.A) = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [e1, _root_.one_mul]
  have hTb : ∀ (χ : Q.X) (j : Fin 4) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ j → T' ≫ A₀.hom = A₀.hom →
      b ≫ T' ≫ m₀ = spMap φ ≫ η[Q.P.A].left ≫ Q.famφB χ j := fun χ j T' h₁ _ => by
    rw [h₁, reassoc_of% hbm]
  have e3 : ∀ (χ : Q.X) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ 3 → T' ≫ A₀.hom = A₀.hom → b ≫ T' = b :=
    fun χ T' h₁ h₂ => P.hom_ext (by rw [Category.assoc, hTb χ 3 T' h₁ h₂, hA3, hbm]) (by rw [Category.assoc, h₂])
  have e0 : ∀ (χ : Q.X) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ 0 → T' ≫ A₀.hom = A₀.hom → b ≫ T' = b :=
    fun χ T' h₁ h₂ => by rw [hF.T_zero h₁ h₂, Category.comp_id]
  have e12 : ∀ (χ : Q.X) (T₁ T₂ : A₀.left ⟶ A₀.left), T₁ ≫ m₀ = m₀ ≫ Q.famφB χ 1 → T₁ ≫ A₀.hom = A₀.hom →
      T₂ ≫ m₀ = m₀ ≫ Q.famφB χ 2 → T₂ ≫ A₀.hom = A₀.hom → b ≫ T₁ = b ≫ T₂ :=
    fun χ T₁ T₂ h₁ h₂ h₃ h₄ => P.hom_ext (by rw [Category.assoc, Category.assoc, hTb χ 1 T₁ h₁ h₂, hTb χ 2 T₂ h₃ h₄, hA12])
      (by rw [Category.assoc, Category.assoc, h₂, h₄])
  have hcov' : ∀ p : Q.P.A.left, ∃ i, p ∈ V i := fun p => by
    have : p ∈ (⨆ i, V i) := by rw [hcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  choose I hI using hcov'
  let p₀ : Q.P.A.left := (b ≫ m₀) z
  let i₀ : h.J := I p₀
  let y : Y.H.left := a z
  have hy : Y.q.left y = p₀ := by
    change (a ≫ Y.q.left) z = _
    rw [w]
  have h₀ : a z ∈ h.W i₀ := by
    rw [hD.1 i₀]
    change Y.q.left y ∈ V i₀
    rw [hy]
    exact hI p₀
  obtain ⟨δ, -, δmul, δeq⟩ := exists_stalkDer_field (isField_dE h ν hF.field i₀) a z h₀
  let π := (a.stalkMap z).hom
  let g := Y.Φ Y.H (𝟙 _)
  let J : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι := fun ψ => h.j (I (ψ y))
  have hJ : Good Q.P.L y J := fun ψ => hV _ (hI _)
  have key : ∀ (χ : Q.X) (c : K), CoordEq Y h ν m₀ V pb χ c →
      δ (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val =
        π (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val * cst (b ≫ A₀.hom) z c := by
    intro χ c Hc
    obtain ⟨T, hT1, hT2⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring χ
    have f0 := e0 χ (T 0) (hT1 0) (hT2 0)
    have f3 := e3 χ (T 3) (hT1 3) (hT2 3)
    have f12 := e12 χ (T 1) (T 2) (hT1 1) (hT2 1) (hT1 2) (hT2 2)
    let i₁ : h.J := I (((b ≫ T 1) ≫ m₀) z)
    let i : Fin 4 → h.J := ![i₀, i₁, i₁, i₀]
    have hpt : ∀ j, (b ≫ T j ≫ m₀) z = Q.famφB χ j p₀ := fun j => by
      rw [hT1 j, ← Category.assoc]; rfl
    have hIi : ∀ j, I ((b ≫ T j ≫ m₀) z) = i j := by
      intro j; fin_cases j
      · show I ((b ≫ T 0 ≫ m₀) z) = i₀; rw [← Category.assoc, f0]
      · show I ((b ≫ T 1 ≫ m₀) z) = i₁; rw [← Category.assoc]
      · show I ((b ≫ T 2 ≫ m₀) z) = i₁; rw [← Category.assoc, ← f12]
      · show I ((b ≫ T 3 ≫ m₀) z) = i₀; rw [← Category.assoc, f3]
    have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => hIi j ▸ hI _
    have Hc' := Hc T hT1 hT2 (Sp K) a b w z i hi
    have hm := hF.mem_chart hD hV hT1 w hi
    unfold CoordAt at Hc'
    have hP : ∀ w' : (Sp K).presheaf.stalk z, - gs (b ≫ T 0) z (m₀ ⁻¹ᵁ V (i 0)) (pb (i 0)) +
        gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V (i 1)) (pb (i 1)) - gs (b ≫ T 2) z (m₀ ⁻¹ᵁ V (i 2)) (pb (i 2)) +
        gs (b ≫ T 3) z (m₀ ⁻¹ᵁ V (i 3)) (pb (i 3)) + w' = w' := by
      intro w'
      rw [f0, f3, ← f12]
      show - gs b z (m₀ ⁻¹ᵁ V i₀) (pb i₀) + gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V i₁) (pb i₁) -
        gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V i₁) (pb i₁) + gs b z (m₀ ⁻¹ᵁ V i₀) (pb i₀) + w' = w'
      ring
    rw [hP] at Hc'
    have hcv : (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val =
        gs (𝟙 _) y (xU Y χ fun j => h.j (i j)) (xc Y χ fun j => h.j (i j)).val := by
      rw [gs_unit (𝟙 _) y _ hm.2]
      congr 1
      refine val_of _ _ _ _ _ fun k => ?_
      show h.j (I ((𝟙 _ ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b χ k) y)) = h.j (i (![1, 2, 0, 3] k))
      rw [Category.id_comp, gtφT_eq, ← hIi, hpt]
      show h.j (I (Q.famφB χ _ (Y.q.left y))) = _
      rw [hy]
    calc δ (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val
        = δ (gs (𝟙 _) y (h.W i₀ ⊓ xU Y χ fun j => h.j (i j))
            (rsT (xc Y χ fun j => h.j (i j)).val (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)))) := by
          rw [hcv, GlobalTheory.KS.DlogPol.gs_rsT (𝟙 Y.H.left) y (O := h.W i₀ ⊓ xU Y χ fun j => h.j (i j)) inf_le_right hm]
      _ = gs a z (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)) (dE h ν i₀ _
            (rsT (xc Y χ fun j => h.j (i j)).val (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)))) := δeq _ inf_le_left hm _
      _ = gs a z (xU Y χ fun j => h.j (i j)) (xc Y χ fun j => h.j (i j)).val * cst (b ≫ A₀.hom) z c := Hc'
      _ = _ := by rw [gs_stalkMap a z _ hm.2, ← hcv]
  have hθ : δ (ReciprocityTheory.ChartRestriction.G.DVR.th Q y J (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H α) (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H β)
      (Y.Φ Y.H (𝟙 _)).b).val = 0 := by
    let Λ : Q.P.A ⟶ Q.P.A ⊗ (Q.P.A ⊗ Q.P.A) :=
      lift (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A α) (lift (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A β) (𝟙 _))
    let G := LB.pullGen Q.P.L (thφ Q.P.A (x3 Q.P.A)) thε Q.cub.t Λ.left
    have a1 : ∀ χ, Y.q ≫ ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A χ = ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H χ := fun χ => by
      simp only [ReciprocityTheory.ChartRestriction.G.DVR.cP, comp_toUnit_assoc]
    have e₁ : ReciprocityTheory.ChartRestriction.G.DVR.th Q y J (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H α) (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H β)
        (Y.Φ Y.H (𝟙 _)).b = val G Y.q.left y J := by
      refine Eq.trans ?_ (val_cub Q.cub Y.q hJ _ _ _).symm
      rw [a1, a1, Category.comp_id]
      rfl
    let j₀ := fun k => J (Y.q.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k)
    let Wc := LB.wchart Q.P.L (fun k => Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) j₀
    let θ₀ : Γ(Q.P.A.left, Wc)ˣ := G.s j₀
    have hWc : Y.q.left y ∈ Wc := hJ.mem _ Y.q.left
    have hp₀W : p₀ ∈ Wc := hy ▸ hWc
    let U : Q.P.A.left.Opens := V i₀ ⊓ Wc
    have hp₀U : p₀ ∈ U := ⟨hI p₀, hp₀W⟩
    have hyU : Y.q.left y ∈ U := hy ▸ hp₀U
    let f : Γ(Q.P.A.left, U) := resG Q.P.A.left (inf_le_right : U ≤ Wc) θ₀.val
    have s1 : (val G Y.q.left y J).val = gs (𝟙 _) y (Y.q.left ⁻¹ᵁ U) ((Y.q.left.app U).hom f) := by
      rw [gs_pull (𝟙 _) Y.q.left y U hyU f, Category.id_comp, gs_res Y.q.left y inf_le_right hyU]
      exact (gs_unit _ _ _ hWc _).symm
    have hle : Y.q.left ⁻¹ᵁ U ≤ h.W i₀ := by
      rw [hD.1 i₀]; exact fun x hx => hx.1
    have s2 := δeq (Y.q.left ⁻¹ᵁ U) hle hyU ((Y.q.left.app U).hom f)
    have s3 := hD.2.1 (Sp K) a b w z i₀ U inf_le_left hp₀U f
    obtain ⟨T, hT1, hT2⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring α
    have f3 := e3 α (T 3) (hT1 3) (hT2 3)
    have hmem3 : (b ≫ T 3 ≫ m₀) z ∈ U := by rw [← Category.assoc, f3]; exact hp₀U
    have s4 := hCm α 3 (T 3) (hT1 3) (hT2 3) U f (Sp K) b z hmem3
    rw [f3] at s4
    have hfix : Q.famφB α 3 p₀ = p₀ := by
      have : (b ≫ T 3 ≫ m₀) z = Q.famφB α 3 p₀ := by rw [hT1 3, ← Category.assoc]; rfl
      rw [← this, ← Category.assoc, f3]
    obtain ⟨δ', -, δ'mul, δ'eq⟩ := exists_stalkDer_along hd b z
    have hc3 : (b ≫ m₀) z ∈ Q.famφB α 3 ⁻¹ᵁ U := by
      show Q.famφB α 3 p₀ ∈ U; rw [hfix]; exact hp₀U
    have s5 := δ'eq _ hc3 ((Q.famφB α 3).app U |>.hom f)
    let C3 : Q.P.A ⟶ Q.P.A := toUnit Q.P.A ≫ η[Q.P.A]
    let J' : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι := fun ψ => h.j (I (ψ p₀))
    have hJ' : Good Q.P.L p₀ J' := fun ψ => hV _ (hI _)
    have hc3' : C3.left p₀ ∈ Wc := by
      show Q.famφB α 3 p₀ ∈ Wc; rw [hfix]; exact hp₀W
    have s6 : gs (𝟙 _) ((b ≫ m₀) z) (Q.famφB α 3 ⁻¹ᵁ U) ((Q.famφB α 3).app U |>.hom f) = 1 := by
      change gs (𝟙 _) p₀ (C3.left ⁻¹ᵁ U) ((C3.left.app U).hom f) = 1
      rw [gs_pull (𝟙 _) C3.left p₀ U (hfix.symm ▸ hp₀U) f, Category.id_comp,
        gs_res C3.left p₀ inf_le_right (hfix.symm ▸ hp₀U), gs_unit _ _ _ hc3']
      have v := val_of G C3.left p₀ J' j₀ fun k => by
        show h.j (I ((C3.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) p₀)) =
          h.j (I ((Y.q.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) y))
        show h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) (C3.left p₀))) =
          h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) (Y.q.left y)))
        rw [hy]; exact congrArg (fun p => h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) p))) hfix
      refine (congrArg Units.val v.symm).trans ?_
      rw [val_cub Q.cub C3 hJ' _ _ _, Category.comp_id, show C3 = 1 from Hom.one_def.symm,
        (isCub_cubV Q.cub hJ').face₃, Units.val_one]
    have δ'1 : δ' 1 = 0 := by
      have := δ'mul 1 1
      simp only [_root_.mul_one, map_one, _root_.one_mul] at this
      linear_combination -this
    rw [e₁, s1, s2, ← s3, ← s4, ← s5, s6, δ'1]
  have E := dlog_const_add π δ δmul _ _ _ _ (GlobalTheory.TorusModel.cv_add (Y.Φ Y.H (𝟙 _)) hJ α β) _ _ _
    (key α c₁ H₁) (key β c₂ H₂) (key (α + β) c₃ H₃) hθ
  rw [cst_eq_cstH, cst_eq_cstH, cst_eq_cstH, ← map_add] at E
  exact (cstH (b ≫ A₀.hom) z).injective E

end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCoordinateInChartsHasCharacterWeight
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false

namespace GlobalTheory.HeatConn.CoordWt

theorem isWt_xc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (α : Q.X) (t : Fin 4 → Q.P.L.ι) (W : Y.H.left.Opens), W ≤ xU Y α t → IsWt Y α W (rsT (xc Y α t).val W) := by
  intro R _ _ Q O _ _ _ oa Y α t W hW
  intro S _ φ x x' c a a' ha ha' hV₁ hV₂ hq hc
  subst ha ha'
  have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ W → ∀ z,
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (valR b W (rsT (xc Y α t).val W))) =
        gs b z (xU Y α t) (xc Y α t).val := by
    intro b hb z
    rw [valR, dif_pos hb, Iso.hom_inv_id_apply, rsT, dif_pos hW]
    refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z W (hb trivial) _).trans ?_)
    rw [Category.id_comp]
    exact gs_res b z hW (hb trivial) _
  have key : ∀ (xx : Over.mk (spMap φ) ⟶ Y.H), ⊤ ≤ xx.left ⁻¹ᵁ W → ∀ z J, Good Q.P.L z J →
      gs xx.left z (xU Y α t) (xc Y α t).val =
        (trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε xx.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (xx.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k))).val *
        (val ((Y.Φ _ xx).s α) (𝟙 _) z J).val := by
    intro xx hb z J hJ
    have hp := ((GlobalTheory.TorusModel.isPull_iff xx _ _).1 (Y.rep.1 _ _ xx (𝟙 _))).2 α z J hJ
    rw [Category.comp_id] at hp
    have hmem : xx.left z ∈ xU Y α t := hW (hb trivial)
    rw [gs_unit xx.left z _ hmem, gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) xx.left z hmem (hJ.mem _ xx.left), Units.val_mul]
    congr 1
    exact congrArg Units.val hp.symm
  have hqq : x'.left ≫ Y.q.left = x.left ≫ Y.q.left := congrArg CommaMorphism.left hq
  have hφ : ∀ k, x'.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k = x.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k :=
    fun k => by rw [gtφT_eq, ← Category.assoc, hqq, Category.assoc]
  have htr : ∀ z (J : (Sp S ⟶ Q.P.A.left) → Q.P.L.ι),
      trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε x'.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (x'.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k)) =
        trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε x.left z (fun k => t (![1, 2, 0, 3] k))
          (fun k => J (x.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k)) := by
    intro z J
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    beta_reduce
    rw [hφ k]
  apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
  refine fn_ext fun z _ => ?_
  obtain ⟨J, hJ, -⟩ := exists_good Q.P.L Q.P.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a _ _ => a.elim) (fun k => k.elim)
  show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
    gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
  rw [map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₂ z, germ _ hV₁ z, key x' hV₂ z J hJ, key x hV₁ z J hJ, htr,
    hc α z J hJ, show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c α : S) = (unitOn (c α)).val from rfl,
    gs_unit (𝟙 _) z ⊤ trivial, Units.val_mul]
  exact _root_.mul_left_comm _ _ _

end GlobalTheory.HeatConn.CoordWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudWeightZeroCompatibleFunctionsEqBaseConstaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaud_weight_zero_compatible_functions_eq_base_constant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (K : Type) (Wk : K → Y.H.left.Opens), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → ∀ F : ∀ k, Γ(Y.H.left, Wk k), (∀ k, IsWt Y 0 _ (F k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (F k) Wo = rsT (F k') Wo) → ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  first | exact @GlobalTheory.Heat.AbConstGlob.main | exact GlobalTheory.Heat.AbConstGlob.main | (intros; apply GlobalTheory.Heat.AbConstGlob.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionMetricSegmentPolynomial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.SelfPoly

open MvPolynomial

theorem eval_pow_expand (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Θ ((C t * X 0 + X 1) ^ (D + 1)) = ∑ i ∈ Finset.range (D + 2),
      t ^ i * ((D + 1).choose i * Θ (X 0 ^ i * X 1 ^ (D + 1 - i))) := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (C t * X 0) ^ i * X 1 ^ (D + 1 - i) * ((D + 1).choose i : MvPolynomial (Fin 2) ℝ)
      = C (t ^ i * (D + 1).choose i) * (X 0 ^ i * X 1 ^ (D + 1 - i)) := by
    rw [C_mul, C_pow, map_natCast]; ring
  rw [this, C_mul', LinearMap.map_smul, smul_eq_mul]; ring

theorem eval_mul_pow_expand (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    Θ (X 0 * (C t * X 0 + X 1) ^ D) = ∑ j ∈ Finset.range (D + 1),
      t ^ j * (D.choose j * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j))) := by
  rw [add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : X 0 * ((C t * X 0) ^ j * X 1 ^ (D - j) * (D.choose j : MvPolynomial (Fin 2) ℝ))
      = C (t ^ j * D.choose j) * (X 0 ^ (j + 1) * X 1 ^ (D - j)) := by
    rw [C_mul, C_pow, map_natCast]; ring
  rw [this, C_mul', LinearMap.map_smul, smul_eq_mul]; ring

def poly (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (D + 2),
    Polynomial.C ((D + 1).choose i * Θ (X 0 ^ i * X 1 ^ (D + 1 - i))) * Polynomial.X ^ i

theorem poly_eval (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    (poly Θ D).eval t = Θ ((C t * X 0 + X 1) ^ (D + 1)) := by
  rw [eval_pow_expand, poly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem poly_derivative_eval (Θ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ) (D : ℕ) (t : ℝ) :
    (poly Θ D).derivative.eval t = ((D : ℝ) + 1) * Θ (X 0 * (C t * X 0 + X 1) ^ D) := by
  rw [eval_mul_pow_expand, poly, map_sum, Polynomial.eval_finsetSum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e₁ : D + 1 - (j + 1) = D - j := Nat.add_sub_add_right D 1 j
  have e₂ : (((D + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) = ((D : ℝ) + 1) * (D.choose j : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq D j).symm
  rw [e₁, Nat.add_sub_cancel]
  calc ((D + 1).choose (j + 1) : ℝ) * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j)) * ((j + 1 : ℕ) : ℝ) * t ^ j
      = (((D + 1).choose (j + 1) : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) * (t ^ j * Θ (X 0 ^ (j + 1) * X 1 ^ (D - j))) := by ring
    _ = _ := by rw [e₂]; ring

end GlobalTheory.HSAmp.SelfPoly

namespace GlobalTheory.HSAmp.SelfPoly

open MvPolynomial HermLB

theorem selfInter_poly : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p) (a a' : ℝ), L.IsSelfInter a → (up L u).IsSelfInter a' →
    ∃ s : Polynomial ℝ, s.eval 0 = a ∧ s.eval 1 = a' ∧
      ∀ t : ℚ, ((D : ℝ) + 1) / 2 * chInt (up L (u.smul t)) D u.u = s.derivative.eval (t : ℝ) := by
  intro H k _ X _ p D hX L u a a' ha ha'
  obtain ⟨Θ, hΘ⟩ := ((H.arExists k X p D hX).2 _ ![fnB u.u u.cInf u.conj, L]).1
  refine ⟨poly Θ D, ?_, ?_, fun t => ?_⟩
  · rw [poly_eval, map_zero, zero_mul, zero_add]
    exact (ha.unique hX (((H.arIso k X p D hX).2 _ _ _ hΘ).1 1)).symm
  · rw [poly_eval, map_one, one_mul]
    have i : (comb ![fnB u.u u.cInf u.conj, L] fun _ => 1).Isometric (up L u) := icls_eq_iff.1 (by
      show _ = (L.raise u.u u.cInf u.conj).icls
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_comb, Fin.sum_univ_two,
        one_smul, one_smul, add_comm]
      rfl)
    rw [ha'.unique hX (i.isSelfInter hX (hΘ.1 _))]
    simp [lin, Fin.sum_univ_two]
  · rw [poly_derivative_eval]
    have hd : (t.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 t.den_nz
    have hq : (t.den : ℝ) * (t : ℝ) = t.num := by
      rw [Rat.cast_def]; field_simp
    let n : Fin 2 → ℤ := ![t.num, t.den]
    have h₁ := GlobalTheory.SelfCont.mixed_eq H hX u.cInf u.conj L hΘ n
    have h₂ := (GlobalTheory.SelfCont.isometric_comb_raise u.cInf u.conj L n).chInt_eq D u.u
    have h₃ : ((zp L (n 1)).raise (fun σ y => (n 0 : ℝ) * u.u σ y) (fun σ y => (u.cInf σ y).const_mul _)
        (GlobalTheory.SelfCont.isConj_mul u.conj _)).Isometric ((up L (u.smul t)).pow t.den) := icls_eq_iff.1 (by
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_pow]
      show _ = t.den • ((L.raise (u.smul t).u (u.smul t).cInf (u.smul t).conj).icls)
      rw [← icls_eq_iff.2 (isometric_tens_fnB _ _ _ _), icls_tens, icls_zp, smul_add, ← natCast_zsmul,
        ← natCast_zsmul, ← GlobalTheory.SelfCont.icls_fnB_mul (u.smul t).cInf (u.smul t).conj]
      congr 1
      refine icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => ?_)
      show (t.den : ℤ) * ((t : ℝ) * u.u σ y) = (t.num : ℝ) * u.u σ y
      rw [← hq]; push_cast; ring)
    have h₄ := GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow k X p D hX (up L (u.smul t)) t.den u.u
    have h₅ : (lin fun i => (n i : ℝ)) = C (t.den : ℝ) * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) := by
      simp only [lin, Fin.sum_univ_two, n, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [mul_add, ← mul_assoc, ← C_mul, hq]; push_cast; ring
    have h₆ : Θ (MvPolynomial.X 0 * (lin fun i => (n i : ℝ)) ^ D) = (t.den : ℝ) ^ D * Θ (MvPolynomial.X 0 * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) ^ D) := by
      rw [h₅, mul_pow, ← C_pow, mul_left_comm, C_mul', LinearMap.map_smul, smul_eq_mul]
    have key : (t.den : ℝ) ^ D * chInt (up L (u.smul t)) D u.u =
        (t.den : ℝ) ^ D * (2 * Θ (MvPolynomial.X 0 * (C (t : ℝ) * MvPolynomial.X 0 + MvPolynomial.X 1) ^ D)) := by
      rw [← h₄, ← h₃.chInt_eq, ← h₂]
      linarith
    have := mul_left_cancel₀ (pow_ne_zero D hd) key
    rw [this]; ring

end GlobalTheory.HSAmp.SelfPoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescentFromCompleteRegularChartsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) → ∃ (G : Over S) (_ : GrpObj G) (e : A.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback A G j e ∧ ∀ (x : S) (C : Chart j A x), ∃ π : C.G.left ⟶ G.left, IsGrpPullback C.G G C.ξ π ∧ C.α ≫ e = pullback.fst C.G.hom (jK C.R) ≫ π := by
  first | exact @GlobalTheory.Desc.descent_semiAbelian | exact GlobalTheory.Desc.descent_semiAbelian | (intros; apply GlobalTheory.Desc.descent_semiAbelian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAtPrimesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_hom_ext_of_localization_at_primes : ∀ (A : Type) [CommRing A] (X : Scheme.{0}) (a b : Sp A ⟶ X), (∀ (P : Ideal A) [P.IsPrime], spMap (algebraMap A (Localization.AtPrime P)) ≫ a = spMap (algebraMap A (Localization.AtPrime P)) ≫ b) → a = b := by
  first | exact @GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime | exact GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime | (intros; apply GlobalTheory.SpecLocalExt.hom_ext_of_localizationAtPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stronger_published_hypotheses_imply : Hypotheses2 → Hypotheses₂ := by
  first | exact @GlobalTheory.CovTop.Hypotheses2.toClassicalTheorems | exact GlobalTheory.CovTop.Hypotheses2.toClassicalTheorems | (intros; apply GlobalTheory.CovTop.Hypotheses2.toClassicalTheorems <;> assumption)
end

