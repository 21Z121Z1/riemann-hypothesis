import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarFiniteTensorEqDatumSmallModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTorsionPointsAdditiveLabel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.PtAdd

theorem x_add : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → ∀ (a τ : X₁.S.Gam) (xτ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), xτ.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left → x (a + τ) = x a * xτ := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x hx a τ xτ hτ
  let U : Over.mk ((TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk (spMap 𝔪.yK) (by
      show spMap 𝔪.yK ≫ 𝟙 _ = _
      rw [Category.comp_id]
      change _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp])
  have key := 𝔪.cart.2 (TFK (R := V) (FractionRing V)) (x a) xτ (U ≫ X₁.ρ.pt a) (U ≫ X₁.ρ.pt τ)
    (hx a).symm hτ.symm
  rw [← MonObj.comp_mul, ← X₁.ρ.pt_add] at key
  apply Over.OverMorphism.ext
  refine 𝔪.cart.1.hom_ext ?_ ?_
  · rw [hx (a + τ), ← key]; rfl
  · rw [Over.w, Over.w]

end GlobalTheory.Poinc.PtAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqSmulIntegralMatrixIndicator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.MixVacSmall

open GlobalTheory.SmallDat GlobalTheory.SmallPlaces
open GlobalTheory.BigDat (atW)

theorem mem_latO_iff_at {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (fS : IsFrame βS ΛS) (fT : IsFrame βT ΛT)
    {w : Pl D.host.E} (he : IsIdemSum (atPl w 1) {w})
    (hw : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (x : WO S T) (hx : IsHalf (atPl w 1) x) :
    x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      ∀ a b, (((loc w βT)⁻¹).val * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (atW w) * (loc w βS).val :
        Matrix (Fin T.rank) (Fin S.rank) (Kw w)) a b ∈ (ValuativeRel.valuation (Kw w)).integer := by
  classical
  rw [GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T ΛS ΛT βS βT hS hT fS fT {w} _ he (by simpa using hw) _ hx]
  have hmap : ∀ Q, (frMapO S T βS βT x).map (cpt (D := D) Q) =
      ((loc Q βT)⁻¹).val * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (atW Q) * (loc Q βS).val := by
    intro Q
    rw [← map_inv]
    unfold frMapO
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  unfold IsIntM
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · have := (mem_OA_iff _).1 (h a b) w
    rw [← hmap, Valuation.mem_integer_iff, (Good.isEquiv_Kw w).le_one_iff_le_one]
    exact this
  · refine (mem_OA_iff _).2 fun Q => ?_
    by_cases hQ : Q = w
    · subst hQ
      have := h a b
      rw [← hmap, Valuation.mem_integer_iff, (Good.isEquiv_Kw Q).le_one_iff_le_one] at this
      exact this
    · have h0 : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (atW Q) = 0 := by
        refine Matrix.ext fun a b => ?_
        calc atW Q (x a b) = atW Q (atPl w 1 * x a b) := congrArg _ (hx a b).symm
          _ = 0 := by rw [map_mul, GlobalTheory.BigDat.atW_atPl_ne hQ, zero_mul]
      have h1 := congrFun (congrFun (hmap Q) a) b
      rw [h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.map_apply, Matrix.zero_apply] at h1
      rw [h1]
      exact zero_mem _

theorem forall_cast_transpose {K : Type} {m m' n n' : ℕ} (hm : m' = m) (hn : n' = n) (A : Matrix (Fin m) (Fin n) K)
    (p : K → Prop) : (∀ r s, p ((A.submatrix (Fin.cast hm) (Fin.cast hn))ᵀ r s)) ↔ ∀ a b, p (A a b) := by
  subst hm hn
  exact forall_comm

theorem mem_latPtS_iff {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (B : Frames G) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) (e : Num G i j) {w : Pl D.host.E} (hw : w ∈ locPl G t)
    {x : PtS G i j} (hx : x ∈ mixHalfS e (atPl w 1)) (hat : At (evFin D.host.F (w.under (𝓞 D.host.F))) x) :
    x ∈ latPtS t e (w.under (𝓞 D.host.F)) ↔ ∀ r s, mixCoS B t e w x r s ∈ (ValuativeRel.valuation (Kw w)).integer := by
  classical
  obtain ⟨_, ⟨es, hes, -⟩, -⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G t
  have h1 : Formalism.L2.NTheta.IsIdemAt (atPl w 1) w := GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hes w hw) ▸ hes w hw
  have he : IsIdemSum (atPl w 1) {w} :=
    ⟨⟨fun _ => atPl w 1, fun PP h => by rw [Finset.mem_singleton] at h; subst h; exact h1, by simp⟩, h1.1.2.1⟩
  have hb : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hst.2 w hw (by
    have := Ideal.mul_mem_left _ ((D.host.d : ℕ) : 𝓞 D.host.E) h
    convert this using 1
    push_cast
    ring)
  have sW : IsSelfDualC (spW₁ G i j) (G.Λ (.grid (i : ℕ) (j : ℕ))) :=
    (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have sV : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have sV₁ : IsSelfDualC (negSp (spV₁ G i j)) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have kA := mem_latO_iff_at sW sV (B.isFrame_β hL i.2.le j.2.le) (B.isFrame_β hL i.2.le j.2) he hb (mapA t e x) hx.1
  have kB := mem_latO_iff_at sV₁ sW (B.isFrame_β hL i.2 j.2.le) (B.isFrame_β hL i.2.le j.2.le) he hb (mapB e x) hx.2
  have cA := forall_cast_transpose (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩)
    (rank_vertex G t w (X := (i, j)) ⟨i.2.le, j.2.le⟩)
    (((loc w (B.β i (j + 1)))⁻¹).val * (mapA t e x).map (atW w) * (loc w (B.β i j)).val)
    (· ∈ (ValuativeRel.valuation (Kw w)).integer)
  have cB := forall_cast_transpose (rank_vertex G t w (X := (i, j)) ⟨i.2.le, j.2.le⟩)
    (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩)
    (((loc w (B.β i j))⁻¹).val * (mapB e x).map (atW w) * (loc w (B.β (i + 1) j)).val)
    (· ∈ (ValuativeRel.valuation (Kw w)).integer)
  rw [mixCoS_eq]
  refine ⟨fun h r s => ?_, fun h => ⟨hat, kA.2 (cA.1 fun r s => h r (.inl s)), kB.2 (cB.1 fun r s => h s (.inr r))⟩⟩
  rcases s with s | s
  · exact cA.2 (kA.1 h.2.1) r s
  · exact cB.2 (kB.1 h.2.2) s r

theorem mixVac_eq_indicator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToB G t i j w, IsMixModelB W B t e Γ w ι →
      ι (Γ.M'.vac _) = ι (Γ.M'.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  intro D T L sc G μ₀ hL W B t i j M hst e Bs Γ X om om' h hT hti w hw I hI
  classical
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  obtain ⟨hid, -⟩ := GlobalTheory.IdemAtPl.main hL (G := G) t
  have hh := halves_split hL W t i j e Γ h.JW₁ h.JWW _ _ (hid w hw).1 (hid w hw).2
  have hco := mixCoS_spec B t i j e w
  have hv := lagr_vac hI (hG.vac _).1 (hG.vac _).2.1 (latPtS t e (w.under (𝓞 D.host.F)) : Set _)
    (fun γ hγ hγ' => VacFix.vac_fixed W M t i j e Bs Γ X om om' h hT _ (latPtS_le_latAtV t i j e Bs Γ X hti _) γ (.inr ⟨hγ, hγ'.elim
      (fun h => ⟨_, (hid w hw).1, h⟩) fun h => ⟨_, splitIdem_conj (hid w hw).1, h⟩⟩)) hco.2.1 hh.2.2.2.1
  funext Z
  obtain ⟨x, hx, rfl⟩ := hco.2.1 Z
  have k := mem_latPtS_iff hL B t i j hst e hw hx (hh.1 x hx)
  refine (hv.2 x hx).trans ?_
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hl : x ∈ latPtS t e (w.under (𝓞 D.host.F))
  · rw [Set.indicator_of_mem hl, Set.indicator_of_mem (s := {Z : MatB G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer})
      (a := mixCoS B t e w x) (k.1 hl), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem (s := {Z : MatB G t i j w | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer})
      (a := mixCoS B t e w x) (fun h' => hl (k.2 h')), mul_zero]

end GlobalTheory.TopFlip.MixVacSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (M : RatModel k Ω) (n : ℕ) (g : M.Z ⟶ PSpace o n) (e : Fin (n + 1) → Ω), PCrd (M.pt ≫ g) e → M.HasDiv e := by
  first | exact @GlobalTheory.UMin.hasDiv_of_pCrd_pt | exact GlobalTheory.UMin.hasDiv_of_pCrd_pt | (intros; apply GlobalTheory.UMin.hasDiv_of_pCrd_pt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSemiAbelianRelDimCotangentVectorBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) Y.t.G.hom ∧ GlobalTheory.VB.IsVB (GlobalTheory.LieVB.omega Y.t.G) (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  first | exact @GlobalTheory.ModelRelDim.relDim_and_isVB_omega | exact GlobalTheory.ModelRelDim.relDim_and_isVB_omega | (intros; apply GlobalTheory.ModelRelDim.relDim_and_isVB_omega <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelValueAtPointOfOpenViaSpecSubalgebraStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelValue_at_point_of_open_via_spec_subalgebra : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (Rs : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp Rs), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap Rs.val.toRingHom) → ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : Rs →+* K), spMap f = q ≫ u₀ → ∀ a : Rs, M.val (q ≫ U₀.ι) (a : Ω) = f a := by
  first | exact @GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap | exact GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap | (intros; apply GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulesIsoOfMatchingFramesStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modules_iso_of_matching_frames : ∀ {X : Scheme.{0}} {F₁ F₂ E : X.Modules} (m₁ : F₁ ⟶ E) (m₂ : F₂ ⟶ E) [Mono m₂] (r : ℕ),
    (∀ x : X, ∃ (U : X.Opens) (s₁ : Fin r → Γ(F₁, U)) (s₂ : Fin r → Γ(F₂, U)), x ∈ U ∧ IsFrame s₁ ∧ IsFrame s₂ ∧
      ∀ j, m₁.app U (s₁ j) = m₂.app U (s₂ j)) →
    ∃ e : F₁ ≅ F₂, e.hom ≫ m₂ = m₁ := by
  first | exact @GlobalTheory.VB.exists_iso_of_frames_app_eq | exact GlobalTheory.VB.exists_iso_of_frames_app_eq | (intros; apply GlobalTheory.VB.exists_iso_of_frames_app_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliGeometricPointEqOfSameFibreActionLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_geometric_point_eq_of_same_fibre_action_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (x x' : Sp K ⟶ Xo.X) (α α' : P.A.left ⟶ Xo.univ.t.G.left), x ≫ Xo.s = x' ≫ Xo.s → IsGrpPullback P.A Xo.univ.t.G x α → IsGrpPullback P.A Xo.univ.t.G x' α' → LBIso P.L (Xo.univ.t.PP.L.pull α) → LBIso P.L (Xo.univ.t.PP.L.pull α') → (∀ a, ∃ h : P.A ⟶ P.A, h.left ≫ α = α ≫ (Xo.univ.t.act.act a).left ∧ h.left ≫ α' = α' ≫ (Xo.univ.t.act.act a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.eta a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.eta a).left) → (∀ a, ∃ z : baseOver (Sp K) ⟶ P.A, z.left ≫ α = x ≫ (Xo.univ.etaA a).left ∧ z.left ≫ α' = x' ≫ (Xo.univ.etaA a).left) → x = x' := by
  first | exact @GlobalTheory.UMin.moduli_point_eq_of_same_fibre | exact GlobalTheory.UMin.moduli_point_eq_of_same_fibre | (intros; apply GlobalTheory.UMin.moduli_point_eq_of_same_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeCoefficientFieldNormalNoetherianSepaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliScheme_coefficientField_normal_noetherian_separated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) , Geo.Tor.IsNormalScheme (Xo.XF c) ∧ IsLocallyNoetherian (Xo.XF c) ∧ (∀ x : Xo.XF c, CharZero ((Xo.XF c).residueField x)) ∧ IsSeparated (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ LocallyOfFiniteType (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ QuasiCompact (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) := by
  first | exact @GlobalTheory.UMin.xF_props | exact GlobalTheory.UMin.xF_props | (intros; apply GlobalTheory.UMin.xF_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFinitePartPullbackStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mono_finite_part_pullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left} (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)), Mono (aH P' x0 hu hπ).left := by
  first | exact @GlobalTheory.FinPartAt.aH_left_mono | exact GlobalTheory.FinPartAt.aH_left_mono | (intros; apply GlobalTheory.FinPartAt.aH_left_mono <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialsDifferByUnitsPositiveBoundaryCombinatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
namespace GlobalTheory.TInj

theorem coneval : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (r m N n : ℕ), 1 ≤ n → ∀ (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin r → ℤ)) (s₁ s₂ : (Fin m ⊕ Fin N) → V) (ga : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)), (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → (∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (a) (b))) → ∃ c₁ c₂ : Fin m → ℕ, (∀ k, 0 < c₁ k) ∧ (∀ k, 0 < c₂ k) ∧ ∑ k, c₁ k • ε (.inl k) = ∑ k, c₂ k • pull ga.toLinearMap (ε (.inl k)) := by
  intro V _ _ _ r m N n hn ε s₁ s₂ ga h1m h1u h2m h2u hprod
  classical
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  let ℓ : FractionRing V → ℤ := fun x => WithZero.log (v x)
  have hinj := IsFractionRing.injective V (FractionRing V)
  have hne : ∀ x : V, x ≠ 0 → algebraMap V (FractionRing V) x ≠ 0 := fun x hx =>
    (map_ne_zero_iff _ hinj).2 hx
  have hv0 : ∀ x : FractionRing V, x ≠ 0 → v x ≠ 0 := fun x hx => (Valuation.ne_zero_iff v).2 hx
  have ℓmul : ∀ x y : FractionRing V, x ≠ 0 → y ≠ 0 → ℓ (x * y) = ℓ x + ℓ y := fun x y hx hy => by
    simp only [ℓ, map_mul, WithZero.log_mul (hv0 x hx) (hv0 y hy)]
  have ℓzpow : ∀ (x : FractionRing V) (z : ℤ), ℓ (x ^ z) = z * ℓ x := fun x z => by
    simp only [ℓ, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  have ℓprod : ∀ (J : Type) (t : Finset J) (g : J → FractionRing V), (∀ i, g i ≠ 0) →
      ℓ (∏ i ∈ t, g i) = ∑ i ∈ t, ℓ (g i) := by
    intro J t g hg
    induction t using Finset.induction_on with
    | empty => simp [ℓ]
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ℓmul _ _ (hg j)
        (Finset.prod_ne_zero_iff.2 fun i _ => hg i), ih]
  have hunit : ∀ x : V, IsUnit x → ℓ (algebraMap V (FractionRing V) x) = 0 := by
    intro x hx
    have h1 : v (algebraMap V (FractionRing V) x) = 1 := by
      refine le_antisymm (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ x) ?_
      by_contra hlt
      have := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).1 (lt_of_not_ge hlt)
      exact (IsLocalRing.mem_maximalIdeal x).1 this hx
    simp only [ℓ, h1, WithZero.log_one]
  have hneg : ∀ x : V, x ∈ maximalIdeal V → x ≠ 0 → ℓ (algebraMap V (FractionRing V) x) < 0 := by
    intro x hm hx
    have h1 : v (algebraMap V (FractionRing V) x) < 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
        (IsDiscreteValuationRing.maximalIdeal V) x).2 hm
    have := (WithZero.log_lt_log (hv0 _ (hne x hx)) one_ne_zero).2 h1
    simpa [ℓ, WithZero.log_one] using this
  have hs0 : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ i, algebraMap V (FractionRing V) (s i) ≠ 0 := by
    intro s hm hu i
    rcases i with k | k
    · exact hne _ (hm k).2
    · exact hne _ (hu k).ne_zero
  have hsum : ∀ (s : (Fin m ⊕ Fin N) → V), (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) →
      (∀ k, IsUnit (s (.inr k))) → ∀ z : (Fin m ⊕ Fin N) → ℤ,
      ℓ (∏ i, algebraMap V (FractionRing V) (s i) ^ z i) =
        ∑ k, z (.inl k) * ℓ (algebraMap V (FractionRing V) (s (.inl k))) := by
    intro s hm hu z
    rw [ℓprod _ _ _ (fun i => zpow_ne_zero _ (hs0 s hm hu i)), Fintype.sum_sum_type]
    simp only [ℓzpow, hunit _ (hu _), mul_zero, Finset.sum_const_zero, add_zero]
  let c₁ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))).toNat
  let c₂ : Fin m → ℕ := fun k => (-ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))).toNat
  have hc₁ : ∀ k, (c₁ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₁ (.inl k))) := fun k => by
    have := hneg _ (h1m k).1 (h1m k).2
    simp only [c₁]; omega
  have hc₂ : ∀ k, (c₂ k : ℤ) = -ℓ (algebraMap V (FractionRing V) (s₂ (.inl k))) := fun k => by
    have := hneg _ (h2m k).1 (h2m k).2
    simp only [c₂]; omega
  refine ⟨c₁, c₂, fun k => ?_, fun k => ?_, ?_⟩
  · have := hc₁ k; have := hneg _ (h1m k).1 (h1m k).2; omega
  · have := hc₂ k; have := hneg _ (h2m k).1 (h2m k).2; omega
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  obtain ⟨u, hu⟩ := hprod a b
  have key := congrArg ℓ hu
  rw [ℓmul _ _ (hne _ u.ne_zero) (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hs0 s₁ h1m h1u i)),
    hunit _ u.isUnit, zero_add, hsum s₂ h2m h2u, hsum s₁ h1m h1u] at key
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, nsmul_eq_mul]
  beta_reduce at key
  have key' : (n:ℤ) * ∑ k, ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = (n:ℤ) * ∑ k, ((c₁ k:ℤ) * ε (.inl k) a b) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₂ k : ℤ) * ε (.inl k) (ga a) (ga b)) = -((n:ℤ) * ε (.inl k) (ga a) (ga b) * ℓ (algebraMap V (FractionRing V) (s₂ (.inl k)))) by rw [hc₂]; ring),
      Finset.sum_congr rfl (fun k _ => show (n:ℤ) * ((c₁ k : ℤ) * ε (.inl k) a b) = -((n:ℤ) * ε (.inl k) a b * ℓ (algebraMap V (FractionRing V) (s₁ (.inl k)))) by rw [hc₁]; ring),
      Finset.sum_neg_distrib, Finset.sum_neg_distrib, key]
  have := (mul_left_cancel₀ hn' key').symm
  exact this

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfMulAtDominantPairCommGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_of_mul_at_dominant_pair_commGroup : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], GlobalTheory.SS.SmConn A → ∀ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left → ∀ (Y : Over (Sp K)) (x₁ x₂ y₁ y₂ : Y ⟶ A), IsDominant (lift x₁ x₂).left → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₁ → u ≫ f = w ≫ y₁) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ x₂ → u ≫ f = w ≫ y₂) → (∀ (Z : Over (Sp K)) (w : Z ⟶ Y) (u : Z ⟶ V), u ≫ j = w ≫ (x₁ * x₂) → u ≫ f = w ≫ (y₁ * y₂)) → ∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f := by
  first | exact @GlobalTheory.Mum.mul_of_isDominant_pair | exact GlobalTheory.Mum.mul_of_isDominant_pair | (intros; apply GlobalTheory.Mum.mul_of_isDominant_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationPullbackFamilyNeZeroOddStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicationPullback_family_ne_zero_odd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ (F₁ : IntFam (maximalIdeal R) D.toPre 1) (G : IntFam (maximalIdeal R) D.toPre (m ^ 2)), MulFam m F₁ G → (∃ α j, (F₁.f α).f j ≠ 0) → ∃ α j, (G.f α).f j ≠ 0 := by
  first | exact @GlobalTheory.Mum.mulFam_exists_ne_zero | exact GlobalTheory.Mum.mulFam_exists_ne_zero | (intros; apply GlobalTheory.Mum.mulFam_exists_ne_zero <;> assumption)
end

