# Informe de compilación y alcance — tercera etapa (8 de noviembre de 2026)

## Entorno

- `lean-toolchain`: Lean 4.35.0.
- `lakefile.toml`: Mathlib v4.35.0 y EllipticPDE en el commit exacto `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- `lake-manifest.json`: Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; EllipticPDE en el commit anterior.
- `lake build TesisPINN.LaplacianoDistribucional`: éxito, código 0.
- `lake build` del objetivo raíz: éxito, código 0, **3166 trabajos**.
- Los `#print axioms` de los once teoremas nuevos enumeran únicamente `[propext, Classical.choice, Quot.sound]`. No aparece `sorryAx`; el módulo nuevo no contiene `sorry`, `admit` ni declaraciones `axiom`.
- `TesisPINN/Energia.lean` conserva SHA256 `DDC5D2DD1A4F3F7E263B4F1CF3E847DFBE039DDAA0AD80A34C06350E6D3CA987`; `EnergiaSobolev.lean` también se conservó sin cambios.

Las advertencias de imports del sistema de módulos y la variable `he` no usada en `Energia.lean` no son errores de compilación.

## Enunciado final comprobado

En el plano `EuclideanSpace ℝ (Fin 2)` y con medida de Lebesgue, para un abierto acotado `Ω`, un error `U : H1Graph.H01 volume Ω` y `r : Lp ℝ 2 (volume.restrict Ω)`, si `ΔU = r` como igualdad de distribuciones abiertas `𝓓′(Ω)`, entonces existe `Cₚ > 0` tal que

`‖U‖_{H¹} ≤ Cₚ √(1 + Cₚ²) ‖r‖_{L²}`.

El enunciado Lean es `energia_sobolev_plano_volumen`. La igualdad distribucional se expresa por `HasDistributionalLaplacian`; `laplaciano_distribucional_l2_unico` prueba que `r` es único, de modo que su norma representa `‖ΔU‖_{L²}`. La definición de `H01` es el cierre de los grafos de funciones de prueba, que es la representación empleada aquí para la pertenencia a `H₀¹`. El dominio Lipschitz de la tesis cumple las hipótesis de abierto acotado; la prueba usa un supuesto geométrico más débil.

## Demostración y control del signo

1. `laplacianoDistribucional` usa `LineDeriv.laplacianCLM` de Mathlib. `laplacianoDistribucional_eq_suma` lo reescribe como `∂₁(∂₁T)+∂₂(∂₂T)` en la base ortonormal de `ℝ²`.
2. `derivadaPrueba` construye la derivada direccional como función de prueba: suavidad por `ContDiff.fderiv_right`, soporte compacto por `HasCompactSupport.fderiv_apply`, y `tsupport` contenido en el original por `tsupport_fderiv_apply_subset`.
3. `H01_le_W12` y `mem_W12_iff_hasWeakFDerivOn` identifican `gradL U` con la primera derivada distribucional de `fnL U`. Por ello `laplaciano_ofFun_eq_div_grad` expresa el laplaciano como divergencia de ese gradiente.
4. La definición de derivada distribucional en Mathlib aplica `∂ᵢ T` a `φ` como `-T(∂ᵢ φ)`. Por tanto `laplaciano_eval_producto` demuestra `⟨ΔU,φ⟩ = -∫ gradL U · ∇φ`. La suma sobre la base se convierte en producto escalar con `OrthonormalBasis.sum_inner_mul_inner`; la integrabilidad necesaria se demuestra localmente.
5. Los lemas `inner_gradiente_prueba_eq_integral` e `inner_residuo_prueba_eq_integral` convierten las integrales en productos `L²(Ω)`; el soporte de `φ` anula las contribuciones externas. `laplaciano_distribucional_implica_prueba` obtiene `HasTestLaplacian U r` con el signo correcto.
6. La prueba de la etapa anterior extiende la identidad de las pruebas al propio `U` por densidad, obtiene Poincaré con constante positiva y aplica `energia_norma_par_debil` a la norma del grafo.

## Clasificación y límites

- **Completo y compilado:** el puente distribucional y la estimación analítica del Lema 3.19 para `ℝ²`, `Ω` abierto acotado, `U ∈ H₀¹` representado por el grafo y `ΔU=r∈L²`. No se asumen `hWeak` ni `hPoincare` en el enunciado final.
- **Condicional previamente verificado:** los lemas hilbertianos de `Energia.lean` conservan sus premisas abstractas; el módulo nuevo las descarga al aplicar el resultado.
- **Pendiente:** identificar la diferencia concreta de las soluciones del Teorema 3.20 con un elemento de `H01` a partir de sus trazas, y formalizar la convergencia probabilística. Tampoco se ha extendido el puente más allá de `ℝ²`.

No se modificó la tesis. Véase `MAPA_VERIFICACION.md` para la cadena de dependencias y las tareas pendientes.

