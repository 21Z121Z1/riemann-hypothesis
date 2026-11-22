import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem res_top_mul {U V : Y.Opens} (hV : V ≤ U) (a : Γ(Y, ⊤)ˣ) (x : Γ(Y, U)ˣ) :
    res hV (res le_top a * x) = res le_top a * res hV x := by
  rw [map_mul, DVR.res_res']

theorem pull_top_res (h : Z ⟶ Y) {U : Y.Opens} {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ U) (a : Γ(Y, ⊤)ˣ) :
    res hW (pullU h U (res le_top a)) = res le_top (Units.map h.appTop.hom.toMonoidHom a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_map]

theorem scaleGenG_one (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε 1 g = g := by
  cases g
  simp only [scaleGenG, map_one, one_mul]

theorem pullGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen t.PP.L φ ε (scaleGenG t φ ε v g) h =
      scaleGenG t (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen t.PP.L φ ε g h) := by
  unfold LB.pullGen scaleGenG
  congr 1
  funext j
  erw [map_mul, map_mul, pull_top_res]

theorem mulGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (φ' : K' → (Y ⟶ t.G.left)) (ε' : K' → ℤ)
    (v v' : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb t.PP.L φ' ε')) :
    LB.mulGen t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g') =
      scaleGenG t _ _ (v * v') (LB.mulGen t.PP.L φ ε φ' ε' g g') := by
  unfold LB.mulGen scaleGenG
  congr 1
  funext j
  erw [res_top_mul, res_top_mul, map_mul, mul_mul_mul_comm]
  rfl

theorem invGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    LB.invGen t.PP.L φ ε (scaleGenG t φ ε v g) = scaleGenG t φ _ v⁻¹ (LB.invGen t.PP.L φ ε g) := by
  unfold LB.invGen scaleGenG
  congr 1
  funext j
  erw [map_inv, mul_inv_rev, mul_comm]
  rfl

theorem corr_scaleGenG {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ}
    {g : LB.Gen (LB.LinComb t.PP.L φ ε)} {g' : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (hc : LB.Gen.Corr t.PP.L φ ε φ' ε' g g') (v : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v g') := by
  intro j j' hj hj' hm
  have e := hc j j' hj hj' hm
  unfold scaleGenG
  dsimp only
  erw [res_top_mul, res_top_mul, e]

theorem scale_eq_of_corr (hL : t.PP.L.IsLB) {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ}
    {g : LB.Gen (LB.LinComb t.PP.L φ ε)} {g' : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (hc : LB.Gen.Corr t.PP.L φ ε φ' ε' g g') {v v' : Γ(Y, ⊤)ˣ}
    (h : LB.Gen.Corr t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g')) : v = v' := by
  refine DVR.units_ext_cover ⊤ (fun ρ => ⊤ ⊓ DVR.piece t.PP.L φ φ' ρ) (fun _ => inf_le_left)
    (DVR.le_iSup_piece t.PP.L φ φ' hL ⊤) v v' fun ρ => ?_
  have hj : LB.Coh t.PP.L φ (ρ ∘ φ) := fun k₁ k₂ e => by simp [e]
  have hj' : LB.Coh t.PP.L φ' (ρ ∘ φ') := fun k₁ k₂ e => by simp [e]
  have hm : ∀ k k', φ k = φ' k' → (ρ ∘ φ) k = (ρ ∘ φ') k' := fun k k' e => by simp [e]
  have e1 := h _ _ hj hj' hm
  have e2 := hc _ _ hj hj' hm
  unfold scaleGenG at e1
  dsimp only at e1
  erw [res_top_mul, res_top_mul, e2, mul_left_inj] at e1
  have e3 := congrArg (res (show ⊤ ⊓ DVR.piece t.PP.L φ φ' ρ ≤
    LB.wchart t.PP.L φ (ρ ∘ φ) ⊓ LB.wchart t.PP.L φ' (ρ ∘ φ') from inf_le_right)) e1
  simpa only [DVR.res_res'] using e3

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem unitΓ_homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (u : Aˣ) :
    Units.map (homAt x0 f).left.appTop.hom.toMonoidHom (unitΓ u) = unitΓ (Units.map f.toMonoidHom u) := by
  ext
  simp only [unitΓ, toΓ, homAt, Over.homMk_left, spMap, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem unitΓ_injective {A : Type} [CommRing A] : Function.Injective (unitΓ (A := A)) := by
  intro u u' h
  ext
  have h1 := congrArg Units.val h
  simp only [unitΓ, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, toΓ] at h1
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom h1
  simpa using h2

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') {d : ℕ}

def mp {n : ℕ} (a : Pt R n d) : Pt R' n d := fun i => map ψ (a i)

private theorem hs_lemma {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) :
    MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

private theorem cz_ev_lemma_2 {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hs_lemma a ha) (fun p => ha p.1 p.2) hf

theorem map_ev' {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d) :
    map ψ (ev a f) = ev (fun j => mp ψ (a j)) (map ψ f) := by
  unfold ev
  exact MvPowerSeries.map_subst (hs_lemma a ha) f

theorem mp_pt {n : ℕ} (j : Fin n) : mp ψ (pt R d j) = pt R' d j := by
  funext i
  simp only [mp, pt, MvPowerSeries.map_X]

theorem mp_zero {n : ℕ} : mp ψ (0 : Pt R n d) = 0 := by
  funext i
  simp [mp]

theorem mp_cons {n m : ℕ} (p : Pt R n d) (u : Fin m → Pt R n d) :
    (fun j => mp ψ (Matrix.vecCons p u j)) = Matrix.vecCons (mp ψ p) (fun j => mp ψ (u j)) := by
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ k => rfl

theorem mp_nil {n : ℕ} : (fun j => mp ψ ((![] : Fin 0 → Pt R n d) j)) = ![] := by
  funext j
  exact j.elim0

theorem cz_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp only [pt, MvPowerSeries.constantCoeff_X]

theorem cz_add (F : Fin d → PS R 2 d) (hF : ∀ i, constantCoeff (F i) = 0) {n : ℕ} (a b : Pt R n d)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin d) :
    constantCoeff (addOf F a b i) = 0 := by
  have h : ∀ (j : Fin 2) (k : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    · exact ha k
    · exact hb k
  show constantCoeff (ev ![a, b] (F i)) = 0
  exact cz_ev_lemma_2 ![a, b] h (F i) (hF i)

theorem cz_comp1 (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0) {n : ℕ} (a : Pt R n d)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) : constantCoeff (comp1 φ a i) = 0 := by
  have h : ∀ (j : Fin 1) (k : Fin d), constantCoeff ((![a] : Fin 1 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    exact ha k
  show constantCoeff (ev ![a] (φ i)) = 0
  exact cz_ev_lemma_2 ![a] h (φ i) (hφ i)

theorem mp_add (F : Fin d → PS R 2 d) {n : ℕ} (a b : Pt R n d)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    mp ψ (addOf F a b) = addOf (fun i => map ψ (F i)) (mp ψ a) (mp ψ b) := by
  funext i
  have h : ∀ (j : Fin 2) (k : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    · exact ha k
    · exact hb k
  show MvPowerSeries.map ψ (ev ![a, b] (F i)) = ev ![mp ψ a, mp ψ b] (MvPowerSeries.map ψ (F i))
  rw [map_ev' ψ _ h]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem mp_comp1 (φ : Pt R 1 d) {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mp ψ (comp1 φ a) = comp1 (mp ψ φ) (mp ψ a) := by
  funext i
  have h : ∀ (j : Fin 1) (k : Fin d), constantCoeff ((![a] : Fin 1 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    exact ha k
  show MvPowerSeries.map ψ (ev ![a] (φ i)) = ev ![mp ψ a] (MvPowerSeries.map ψ (φ i))
  rw [map_ev' ψ _ h]
  congr 1
  funext j
  fin_cases j
  rfl

def mapG (G : FGLaw R d) : FGLaw R' d where
  F := fun i => map ψ (G.F i)
  const := fun i => by rw [constantCoeff_map, G.const i, map_zero]
  unit := fun i => by
    have h := congrArg (map ψ) (G.unit i)
    rw [map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt]), mp_cons, mp_cons, mp_nil, mp_zero, mp_pt,
      map_X] at h
    exact h
  comm := fun i => by
    have h := congrArg (map ψ) (G.comm i)
    rw [map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt]), mp_cons, mp_cons, mp_nil, mp_pt, mp_pt] at h
    exact h
  assoc := fun i => by
    have h := G.assoc i
    change ev ![addOf G.F (pt R d 0) (pt R d 1), pt R d 2] (G.F i) =
      ev ![pt R d 0, addOf G.F (pt R d 1) (pt R d 2)] (G.F i) at h
    have h2 := congrArg (map ψ) h
    rw [map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt, cz_add _ G.const]),
      map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt, cz_add _ G.const]),
      mp_cons, mp_cons, mp_nil, mp_cons, mp_cons, mp_nil, mp_add ψ _ _ _ (cz_pt _) (cz_pt _),
      mp_add ψ _ _ _ (cz_pt _) (cz_pt _), mp_pt, mp_pt, mp_pt] at h2
    exact h2

def mapA {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : OAct O (mapG ψ G) where
  act := fun a => mp ψ (A.act a)
  const := fun a i => by
    show constantCoeff (map ψ (A.act a i)) = 0
    rw [constantCoeff_map, A.const a i, map_zero]
  hom := fun a => by
    have h := congrArg (mp ψ) (A.hom a)
    simp only [FGLaw.add] at h
    rw [mp_comp1 ψ _ _ (cz_add _ G.const _ _ (cz_pt _) (cz_pt _)), mp_add ψ _ _ _ (cz_pt _) (cz_pt _),
      mp_add ψ _ _ _ (cz_comp1 _ (A.const a) _ (cz_pt _)) (cz_comp1 _ (A.const a) _ (cz_pt _)),
      mp_comp1 ψ _ _ (cz_pt _), mp_comp1 ψ _ _ (cz_pt _), mp_pt, mp_pt] at h
    exact h
  add_act := fun a b => by
    have h := congrArg (mp ψ) (A.add_act a b)
    simp only [FGLaw.add] at h
    rw [mp_add ψ _ _ _ (A.const a) (A.const b)] at h
    exact h
  mul_act := fun a b => by
    have h := congrArg (mp ψ) (A.mul_act a b)
    rw [mp_comp1 ψ _ _ (A.const b)] at h
    exact h
  one_act := by
    have h := congrArg (mp ψ) A.one_act
    rw [mp_pt] at h
    exact h

section FB

variable {O : Type} [CommRing O] [StarRing O] (B : FB R d O)

local macro "fbm" : tactic => `(tactic| (simp only [map_mul, map_one, FGLaw.add, map_ev', mp_cons, mp_nil, mp_pt, mp_zero,
    mp_add, mp_comp1, Fin.forall_fin_succ, IsEmpty.forall_iff, Matrix.cons_val_zero, Matrix.cons_val_succ, cz_pt,
    cz_add _ B.G.const, cz_comp1 _ (B.A.const _), map_zero, Pi.zero_apply, implies_true, and_self, forall_const, true_and]
    at *))

set_option maxHeartbeats 1000000 in

def mapFB : FB R' d O where
  G := mapG ψ B.G
  A := mapA ψ B.A
  ph1 := map ψ B.ph1
  ph2 := map ψ B.ph2
  sy := map ψ B.sy
  ad := fun a => map ψ (B.ad a)
  cocycleLeft_zero_fst := by have h := congrArg (map ψ) B.cocycleLeft_zero_fst; fbm; exact h
  cocycleLeft_zero_snd := by have h := congrArg (map ψ) B.cocycleLeft_zero_snd; fbm; exact h
  cocycleLeft_zero_thd := by have h := congrArg (map ψ) B.cocycleLeft_zero_thd; fbm; exact h
  cocycleRight_zero_fst := by have h := congrArg (map ψ) B.cocycleRight_zero_fst; fbm; exact h
  cocycleRight_zero_snd := by have h := congrArg (map ψ) B.cocycleRight_zero_snd; fbm; exact h
  cocycleRight_zero_thd := by have h := congrArg (map ψ) B.cocycleRight_zero_thd; fbm; exact h
  symmetry_zero_fst := by have h := congrArg (map ψ) B.symmetry_zero_fst; fbm; exact h
  symmetry_zero_snd := by have h := congrArg (map ψ) B.symmetry_zero_snd; fbm; exact h
  adjoint_zero_fst := fun a => by have h := congrArg (map ψ) (B.adjoint_zero_fst a); fbm; exact h
  adjoint_zero_snd := fun a => by have h := congrArg (map ψ) (B.adjoint_zero_snd a); fbm; exact h
  cocycleLeft_assoc := by have h := congrArg (map ψ) B.cocycleLeft_assoc; fbm; exact h
  cocycleLeft_comm := by have h := congrArg (map ψ) B.cocycleLeft_comm; fbm; exact h
  cocycleRight_assoc := by have h := congrArg (map ψ) B.cocycleRight_assoc; fbm; exact h
  cocycleRight_comm := by have h := congrArg (map ψ) B.cocycleRight_comm; fbm; exact h
  interchange := by have h := congrArg (map ψ) B.interchange; fbm; exact h
  sy_inv := by have h := congrArg (map ψ) B.sy_inv; fbm; exact h
  sy_law := by have h := congrArg (map ψ) B.sy_law; fbm; exact h
  adjoint_compat_left := fun a => by have h := congrArg (map ψ) (B.adjoint_compat_left a); fbm; exact h
  adjoint_compat_right := fun a => by have h := congrArg (map ψ) (B.adjoint_compat_right a); fbm; exact h
  ad_one := by show map ψ (B.ad 1) = 1; rw [B.ad_one, map_one]
  ad_mul := fun a b => by have h := congrArg (map ψ) (B.ad_mul a b); fbm; exact h
  ad_add := fun a b => by have h := congrArg (map ψ) (B.ad_add a b); fbm; exact h
  ad_sy := fun a => by have h := congrArg (map ψ) (B.ad_sy a); fbm; exact h

end FB

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem fbMap_holds : FBMapSt := by
  intro R R' _ _ ψ d O _ _ B
  exact ⟨FBMap.mapFB ψ B, fun j => rfl, fun a j => rfl, rfl, rfl, rfl, fun a => rfl⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupOnCopies
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace FormalGroupOnCopies

def OnCopies {k : Type} [CommRing k] {n d : ℕ} (S : Finset (Fin n)) (f : PS k n d) : Prop :=
  ∀ mm : Fin n × Fin d →₀ ℕ, coeff mm f ≠ 0 → ∀ i ∈ mm.support, i.1 ∈ S

end FormalGroupOnCopies

open FormalGroupOnCopies

def ColumnsStatement : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O),
    constantCoeff (B.hL k h w0) = 0 →
    ∀ (m n : ℕ) (S : Finset (Fin n)) (f₁ f₂ : PS k n d) (ι : Type) [Fintype ι]
      (cp : ι → Fin n) (u : ι → Fin d → k) (P₁ P₂ : MvPolynomial ι k),
      OnCopies S f₁ → OnCopies Sᶜ f₂ → (∀ l ∈ P₁.vars, cp l ∈ S) → (∀ l ∈ P₂.vars, cp l ∉ S) →
      nabValN B k h w0 m (f₁ * f₂) cp u (P₁ * P₂) =
        nabValN B k h w0 m f₁ cp u P₁ * nabValN B k h w0 m f₂ cp u P₂

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeBeta
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def BetaUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (a : 𝓞 E) (β β' : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε)),
    β.IsGen → β'.IsGen →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β' (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    β = β'

namespace GaugeBeta

theorem pull_unit_eq_one_k {X Y S0 : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : S0 ⟶ Y) (ψ : S0 ⟶ X) (k : ℤ)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => k))
    (t t' : LB.Gen (LB.LinComb L φ ε)) (u : Γ(Y, ⊤)ˣ)
    (hu : ∀ j, t.s j = res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) u * t'.s j)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) rig)
    (hc' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' h) rig) :
    (h.app ⊤).hom (u : Γ(Y, ⊤)) = 1 := by

  let rig1 : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1) := ⟨rig.s⟩
  exact pull_unit_eq_one L hL φ ε h ψ rig1 t t' u hu hc hc'

end GaugeBeta

theorem betaUniq_of_global (hglob : GlobalFnsSt) : BetaUniqSt := by
  intro E _ _ _ H Dw l Xo a β β' hβ hβ' hc hc'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨u, hu⟩ := gen_ratio _ (wchart_cover Xo.univ.t.PP.L hL _) β β' hβ hβ'
  have h1 := GaugeBeta.pull_unit_eq_one_k Xo.univ.t.PP.L hL _ _ (eSec Xo.univ.t.G)
    (eSec Xo.univ.t.G) (-3) (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) β β' u hu hc hc'
  have hu1 : u = 1 := by
    obtain ⟨v, hv⟩ := (hglob _ Xo.univ.t.G (isAbelianScheme_univ Xo)).2 (u : Γ(Xo.univ.t.G.left, ⊤))
    have hw : eSec Xo.univ.t.G ≫ Xo.univ.t.G.hom = 𝟙 _ := by
      unfold eSec
      exact Over.w _
    have e1 : (Scheme.Hom.app (eSec Xo.univ.t.G) ⊤).hom
        ((Scheme.Hom.appTop Xo.univ.t.G.hom).hom v) = v := by
      have := congrArg (fun f => (Scheme.Hom.appTop f).hom v) hw
      simp at this
      exact this
    rw [hv] at e1
    have hv1 : v = 1 := e1.symm.trans h1
    apply Units.ext
    rw [← hv, hv1, map_one]
    rfl
  cases β
  cases β'
  congr 1
  funext j
  have hj := hu j
  rw [hu1, map_one, one_mul] at hj
  exact hj

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

