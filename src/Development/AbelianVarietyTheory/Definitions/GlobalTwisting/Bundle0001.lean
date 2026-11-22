import Mathlib

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm
section
noncomputable section

open scoped ContDiff Matrix

namespace GlobalTheory.BorelCoh

section Complex

variable {C : ℕ → Type} [∀ q, AddCommGroup (C q)] [∀ q, Module ℂ (C q)]

def IsBd (d : ∀ q, C q → C (q + 1)) (T : ∀ q, Set (C q)) : (q : ℕ) → C q → Prop
  | 0, c => c = 0
  | q + 1, c => ∃ η ∈ T q, d q η = c

def CohGE (d : ∀ q, C q → C (q + 1)) (T : ∀ q, Set (C q)) (q n : ℕ) : Prop :=
  ∃ w : Fin n → C q, (∀ i, w i ∈ T q ∧ d q (w i) = 0) ∧ ∀ c : Fin n → ℂ, IsBd d T q (∑ i, c i • w i) → c = 0

end Complex

section Rel

variable {P M : Type} [AddCommGroup P] [Module ℝ P] [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

def gd (L : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (f : P [⋀^Fin q]→ₗ[ℝ] M) : P [⋀^Fin (q + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin
    { toFun := fun X => ((L X).restrictScalars ℝ).compAlternatingMap f
      map_add' := fun X Y => AlternatingMap.ext fun v => LinearMap.congr_fun (map_add L X Y) (f v)
      map_smul' := fun c X => AlternatingMap.ext fun v => LinearMap.congr_fun (map_smul L c X) (f v) }

def relCo {K : Type} (ad : K → P → P) (κ : K → Module.End ℂ M) (S : Submodule ℂ M) (q : ℕ) :
    Set (P [⋀^Fin q]→ₗ[ℝ] M) :=
  {f | (∀ k X, f (fun i => ad k (X i)) = κ k (f X)) ∧ ∀ X, f X ∈ S}

def basicCo {K : Type} (ad : K → P → P) (κ : K → Module.End ℂ M) (S : Submodule ℂ M) (L : P →ₗ[ℝ] Module.End ℂ M)
    (Z : P) (q : ℕ) : Set (P [⋀^Fin q]→ₗ[ℝ] M) :=
  {f | f ∈ relCo ad κ S q ∧ (∀ X i, X i = Z → f X = 0) ∧ ∀ X, L Z (f X) = 0}

end Rel

section Forms

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : Type} {d : ℕ}

abbrev Form (V Y : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d q : ℕ) : Type :=
  Y → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)

def formD (O : Set V) {q : ℕ} (α : Form V Y d q) : Form V Y d (q + 1) :=
  fun y => O.indicator (extDeriv (α y))

def invForm (O : Set V) {Γ : Type} [Group Γ] [MulAction Γ Y] (σ : Γ → V →L[ℝ] V) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ)
    (q : ℕ) : Set (Form V Y d q) :=
  {α | (∀ y, ∀ x ∉ O, α y x = 0) ∧ (∀ y, ContDiffOn ℝ ∞ (α y) O) ∧
    ∀ γ y x (X : Fin q → V), α (γ • y) (σ γ x) (fun i => σ γ (X i)) = ξ γ *ᵥ α y x X}

def basicForm (O : Set V) {Γ : Type} [Group Γ] [MulAction Γ Y] (σ : Γ → V →L[ℝ] V) (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ)
    (q : ℕ) : Set (Form V Y d q) :=
  {α | α ∈ invForm O σ ξ q ∧ (∀ y x (X : Fin q → V) i, X i = x → α y x X = 0) ∧
    ∀ y x (X : Fin q → V) (s : ℝ), 0 < s → α y (s • x) (fun i => s • X i) = α y x X}

end Forms

section Group

variable (𝕜 ι : Type) [RCLike 𝕜] [Fintype ι] (a : ℕ)

abbrev Mat : Type := Fin a → Fin a → ι → 𝕜

def hermV : Submodule ℝ (Mat 𝕜 ι a) where
  carrier := {x | ∀ i j, x j i = star (x i j)}
  add_mem' {x y} hx hy i j := by simp [hx i j, hy i j]
  zero_mem' i j := by simp
  smul_mem' c x hx i j := by
    funext t
    have h := congrFun (hx i j) t
    simp only [Pi.smul_apply, Pi.star_apply] at h ⊢
    rw [h, RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, star_mul', RCLike.star_def, RCLike.conj_ofReal]

def posSet : Set (hermV 𝕜 ι a) := {p | ∃ g : GL (Fin a) (ι → 𝕜), (p : Mat 𝕜 ι a) = Matrix.of.symm (g.val * g.valᴴ)}

variable {𝕜 ι a}

def invSet : Set (Mat 𝕜 ι a) := {x | IsUnit (Matrix.of x)}

def lmulH (x : Mat 𝕜 ι a) : hermV 𝕜 ι a →L[ℝ] Mat 𝕜 ι a :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.mulLeft ℝ (Matrix.of x) : Matrix (Fin a) (Fin a) (ι → 𝕜) →ₗ[ℝ] _) ∘ₗ (hermV 𝕜 ι a).subtype)

variable (𝕜 ι a) in

abbrev GCo (Y : Type) (d q : ℕ) : Type := Y → Mat 𝕜 ι a → hermV 𝕜 ι a [⋀^Fin q]→L[ℝ] (Fin d → ℂ)

def gDiff {Y : Type} {d q : ℕ} (w : GCo 𝕜 ι a Y d q) : GCo 𝕜 ι a Y d (q + 1) :=
  fun y => invSet.indicator fun x => ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ (w y) x).comp (lmulH x))

def gCo {Y H : Type} [Group H] [MulAction H Y] (ρ : H →* GL (Fin a) (ι → 𝕜)) {d : ℕ} (ξ : H →* Matrix (Fin d) (Fin d) ℂ)
    (K₀ : Set (Matrix.unitaryGroup (Fin a) (ι → 𝕜))) (q : ℕ) : Set (GCo 𝕜 ι a Y d q) :=
  {w | (∀ y, ∀ x ∉ invSet, w y x = 0) ∧ (∀ y, ContDiffOn ℝ ∞ (w y) invSet) ∧
    (∀ k ∈ K₀, ∀ y x (X X' : Fin q → hermV 𝕜 ι a),
      (∀ i, (X' i : Mat 𝕜 ι a) = Matrix.of.symm (k.val * Matrix.of (X i : Mat 𝕜 ι a) * star k.val)) →
      w y (Matrix.of.symm (Matrix.of x * k.val)) X = w y x X') ∧
    (∀ h y x X, w (h • y) (Matrix.of.symm ((ρ h).val * Matrix.of x)) X = ξ h *ᵥ w y x X) ∧
    (∀ y x (X : Fin q → hermV 𝕜 ι a) i, (X i : Mat 𝕜 ι a) = Matrix.of.symm 1 → w y x X = 0) ∧
    ∀ y x X (s : ℝ), 0 < s → w y (s • x) X = w y x X}

def conjL (g : GL (Fin a) (ι → 𝕜)) : hermV 𝕜 ι a →L[ℝ] hermV 𝕜 ι a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => ⟨Matrix.of.symm (g.val * Matrix.of (p : Mat 𝕜 ι a) * g.valᴴ), fun i j => by
        have hp : (Matrix.of (p : Mat 𝕜 ι a))ᴴ = Matrix.of (p : Mat 𝕜 ι a) :=
          Matrix.ext fun k l => (p.2 l k).symm
        have h := congrArg (fun m : Matrix (Fin a) (Fin a) (ι → 𝕜) => m j i)
          (show (g.val * Matrix.of (p : Mat 𝕜 ι a) * g.valᴴ)ᴴ = g.val * Matrix.of (p : Mat 𝕜 ι a) * g.valᴴ by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hp, Matrix.mul_assoc])
        exact h.symm⟩
      map_add' := fun p p' => Subtype.ext (funext fun i => funext fun j => by
        change (g.val * (Matrix.of (p : Mat 𝕜 ι a) + Matrix.of (p' : Mat 𝕜 ι a)) * g.valᴴ) i j = _
        rw [Matrix.mul_add, Matrix.add_mul]; rfl)
      map_smul' := fun c p => Subtype.ext (funext fun i => funext fun j => by
        change (g.val * (c • Matrix.of (p : Mat 𝕜 ι a)) * g.valᴴ) i j = _
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl) }

def funRep {Γ : Type} [Group Γ] (Y : Type) [MulAction Γ Y] {d : ℕ} (ξ : Γ →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ Γ (Y → Fin d → ℂ) where
  toFun γ :=
    { toFun := fun f y => ξ γ *ᵥ f (γ⁻¹ • y)
      map_add' := fun f g => funext fun y => by simp [Matrix.mulVec_add]
      map_smul' := fun c f => funext fun y => by simp [Matrix.mulVec_smul] }
  map_one' := by ext f y; simp
  map_mul' γ δ := by ext f y; simp [mul_smul]

end Group

end GlobalTheory.BorelCoh

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CocyclesCyclotomicFinrankThree
section
noncomputable section

namespace GlobalTheory.OrdLoc

variable {G : Type} [Group G] [TopologicalSpace G] (E : Type) [NontriviallyNormedField E]

def WCont {X M : Type} [TopologicalSpace X] [AddCommGroup M] [Module E M] (f : X → M) : Prop :=
  ∀ ℓ : M →ₗ[E] E, Continuous fun x => ℓ (f x)

variable {E}

def Z1 (γ : G →* Eˣ) : Submodule E (G → E) where
  carrier := {c | Continuous c ∧ ∀ g h, c (g * h) = c g + (γ g : E) * c h}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨ha.add hb, fun g h => by simp only [Pi.add_apply, ha', hb']; ring⟩
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  smul_mem' := by
    rintro t a ⟨ha, ha'⟩
    exact ⟨continuous_const.mul ha, fun g h => by simp only [Pi.smul_apply, smul_eq_mul, ha']; ring⟩

def IsCoc2 (γ : G →* Eˣ) (c : G × G → E) : Prop :=
  Continuous c ∧ ∀ g h k, (γ g : E) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0

def IsCob2 (γ : G →* Eˣ) (c : G × G → E) : Prop :=
  ∃ b : G → E, Continuous b ∧ ∀ g h, c (g, h) = (γ g : E) * b h - b (g * h) + b g

structure TateChar (ε : G →* Eˣ) : Prop where
  h2_vanish_nontrivial : ∀ γ : G →* Eˣ, Continuous (fun g => (γ g : E)) → γ ≠ ε → ∀ c, IsCoc2 γ c → IsCob2 γ c
  h2_one_dimensional_cyclotomic : ∀ c c', IsCoc2 ε c → IsCoc2 ε c' → ∃ a b : E, (a ≠ 0 ∨ b ≠ 0) ∧ IsCob2 ε (a • c + b • c')
  cocycles_finrank_two : ∀ γ : G →* Eˣ, Continuous (fun g => (γ g : E)) → γ ≠ ε → Module.finrank E (Z1 γ) = 2
  cocycles_cyclotomic_finrank_three : Module.finrank E (Z1 ε) = 3

def IsCocOn (I : Subgroup G) (ε : G →* Eˣ) (c : G → E) : Prop :=
  ContinuousOn c I ∧ ∀ s ∈ I, ∀ t ∈ I, c (s * t) = c s + (ε s : E) * c t

structure IsKummerVal (I : Subgroup G) (ε : G →* Eˣ) (val : (G → E) →ₗ[E] E) (κ : G → E) : Prop where
  congr : ∀ c c' : G → E, (∀ s ∈ I, c s = c' s) → val c = val c'
  cob : val (fun s => (ε s : E) - 1) = 0
  conj : ∀ c, IsCocOn I ε c → ∀ g : G, val (fun s => (ε g : E) * c (g⁻¹ * s * g)) = val c
  kap_mem : κ ∈ Z1 ε
  kap_val : val κ = 1

structure IsFrobData [IsTopologicalGroup G] (I : Subgroup G) (φ : G) (ν : G → E) : Prop where
  dense : (Subgroup.zpowers φ ⊔ I).topologicalClosure = ⊤
  nu_cont : Continuous ν
  nu_add : ∀ g h, ν (g * h) = ν g + ν h
  nu_I : ∀ s ∈ I, ν s = 0
  nu_phi : ν φ = 1

variable (G E) in

structure LocD [IsTopologicalGroup G] where
  I : Subgroup G
  Gv : Subgroup G
  ε : G →* Eˣ
  ψ : G →* Eˣ
  φ : G
  ν : G → E
  val : (G → E) →ₗ[E] E
  κ : G → E
  s0 : G
  I_normal : I.Normal
  I_le : I ≤ Gv
  Gv_open : IsOpen (Gv : Set G)
  Gv_two : ∀ g h, g ∉ Gv → h ∉ Gv → g * h ∈ Gv
  eps_cont : Continuous fun g => (ε g : E)
  psi_cont : Continuous fun g => (ψ g : E)
  tate : TateChar ε
  kum : IsKummerVal I ε val κ
  frob : IsFrobData I φ ν
  decompSigma_mem : s0 ∈ I
  char_sq_ne_one : ψ s0 ^ 2 ≠ 1
  eps_ne : ∃ s ∈ I, ε s ≠ 1
  sq_ne : ∃ s ∈ I, ψ s ^ 2 ≠ ε s

end GlobalTheory.OrdLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ContFromConst
section
noncomputable section

open scoped NNReal

namespace GlobalTheory.EisGen

variable {G : Type} [TopologicalSpace G]

def LocReg (ht : G → ℝ≥0) (Ei : ℂ → G → ℂ) : Prop :=
  ∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → G → ℂ), 0 < r ∧
    (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Ei s g) ∧
    (∀ g, DifferentiableOn ℂ (fun s => H s g) (Metric.ball s₀ r)) ∧
    ContinuousOn (fun x : ℂ × G => H x.1 x.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ g, ‖H s g‖ ≤ C * (ht g : ℝ) ^ N

def ContFrom (ht : G → ℝ≥0) (σ₀ : ℝ) (e : ℂ → G → ℂ) : Prop :=
  ∃ Ei : ℂ → G → ℂ, (∀ s : ℂ, σ₀ < s.re → ∀ g, Ei s g = e s g) ∧ LocReg ht Ei

theorem ContFrom.mono {ht : G → ℝ≥0} {σ₀ σ₁ : ℝ} {e : ℂ → G → ℂ} (h : ContFrom ht σ₀ e) (hσ : σ₀ ≤ σ₁) : ContFrom ht σ₁ e :=
  let ⟨Ei, h1, h2⟩ := h
  ⟨Ei, fun s hs => h1 s (hσ.trans_lt hs), h2⟩

variable (E : Type) [Field E] (n : ℕ) in

def diagCols : Matrix (Fin (n + n)) (Fin n) E :=
  (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E)).submatrix finSumFinEquiv.symm id

end GlobalTheory.EisGen

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle
section
noncomputable section

open CategoryTheory

namespace GlobalTheory.HomStab

variable {k G : Type} [CommRing k] [Group G]

def permRep (X : Type) [MulAction G X] (A : Rep k G) : Representation k G (X →₀ A.V) where
  toFun g := Finsupp.lmapDomain A.V k (g • ·) ∘ₗ Finsupp.mapRange.linearMap (A.ρ g)
  map_one' := by ext x a; simp
  map_mul' g h := by ext x a; simp [mul_smul]

@[simp] theorem permRep_single {X : Type} [MulAction G X] (A : Rep k G) (g : G) (x : X) (a : A.V) :
    permRep X A g (Finsupp.single x a) = Finsupp.single (g • x) (A.ρ g a) := by
  simp [permRep]

abbrev permT (X : Type) [MulAction G X] (A : Rep k G) : Rep k G := Rep.of (permRep X A)

variable (k G) in

abbrev perm (X : Type) [MulAction G X] : Rep k G := permT X (Rep.trivial k G k)

def permCoef (X : Type) [MulAction G X] {A B : Rep k G} (f : A ⟶ B) : permT X A ⟶ permT X B :=
  Rep.ofHom ⟨Finsupp.mapRange.linearMap f.hom.toLinearMap, fun g => by
    ext x a; simp [Rep.hom_comm_apply f]⟩

def permMap {X Y : Type} [MulAction G X] [MulAction G Y] (f : X → Y) (hf : ∀ (g : G) x, f (g • x) = g • f x)
    (A : Rep k G) : permT X A ⟶ permT Y A :=
  Rep.ofHom ⟨Finsupp.lmapDomain A.V k f, fun g => by ext x a; simp [hf]⟩

def ptMap {H X : Type} [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x) (A : Rep k G) :
    Rep.res φ A ⟶ Rep.res φ (permT X A) :=
  Rep.ofHom ⟨Finsupp.lsingle x, fun h => LinearMap.ext fun a => by
    change Finsupp.single x (A.ρ (φ h) a) = permRep X A (φ h) (Finsupp.single x a)
    rw [permRep_single, hx]⟩

variable (k) in

def ptH {H X : Type} [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x) (n : ℕ) :
    groupHomology (Rep.trivial k H k) n ⟶ groupHomology (perm k G X) n :=
  groupHomology.map (A := Rep.trivial k H k) φ (ptMap φ x hx (Rep.trivial k G k)) n

abbrev hMap {A B : Rep k G} (f : A ⟶ B) (n : ℕ) : groupHomology A n ⟶ groupHomology B n :=
  groupHomology.map (MonoidHom.id G) f n

end GlobalTheory.HomStab

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
section
noncomputable section

open scoped Matrix

namespace GlobalTheory.SeqCx

def bd (V : Type) : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun l : List V =>
    ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) (1 : ℤ)

def chains {V : Type} (F : Set (List V)) (p : ℕ) : Submodule ℤ (List V →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {l | l ∈ F ∧ l.length = p}

def ExactAt {V : Type} (F : Set (List V)) (p : ℕ) : Prop :=
  ∀ c ∈ chains F p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c

def SubClosed {V : Type} (F : Set (List V)) : Prop := ∀ l ∈ F, ∀ l' : List V, l'.Sublist l → l' ∈ F

def linkIn {V : Type} (F : Set (List V)) (S : Set V) (τ : List V) : Set (List V) :=
  {w | (∀ x ∈ w, x ∈ S) ∧ τ ++ w ∈ F}

def uniSeq (R : Type) [CommRing R] (n : ℕ) : Set (List (Fin n → R)) :=
  {l | ∃ f : Fin l.length → Fin n → R, ∀ i j : Fin l.length, f i ⬝ᵥ l.get j = if i = j then 1 else 0}

def splitSeq (R : Type) [CommRing R] (n : ℕ) : Set (List ((Fin n → R) × (Fin n → R))) :=
  {l | ∀ i j : Fin l.length, (l.get i).2 ⬝ᵥ (l.get j).1 = if i = j then 1 else 0}

example : [((fun _ => 1 : Fin 1 → ℤ), (fun _ => 1 : Fin 1 → ℤ))] ∈ splitSeq ℤ 1 := by
  intro i j
  obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
  fin_cases i
  simp [dotProduct]

end GlobalTheory.SeqCx

end
end

