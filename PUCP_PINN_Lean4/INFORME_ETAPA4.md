# Cuarta etapa: Dirichlet exacto en `(-1,1)²`

Fecha: 8 de noviembre de 2026 (hora de Lima). Base: PR borrador #5, revisión `2cda6715ff98a48409f4102cfc5308d7588d6027`.

## Correspondencia con la tesis

- **Lema 3.19, (3.71):** para `e∈H₀¹(U)` y `Δe∈L²(U)`, `‖e‖H¹ ≤ Cₚ √(1+Cₚ²) ‖Δe‖L²`. Ya estaba demostrado para abiertos acotados de `ℝ²` en `LaplacianoDistribucional.lean`.
- **Teorema 3.20, (3.74):** con Dirichlet exacto, el error `e=hₘ-u*` tiene traza cero y `Δe=Δhₘ-f`. La cota determinista tiene la misma forma. La afirmación posterior de convergencia casi segura y tasa usa además la Hipótesis 3.7, minimizadores medibles y muestreo; esta etapa no la demuestra.
- **Corolario 3.23, (3.80):** la constante óptima para el cuadrado es `Cₚ=√2/π`, deducida en la tesis de la primera autofrecuencia `π²/2`. El código actual obtiene una constante positiva, sin certificar la óptima.

## Código y compilación

Se agregó `TesisPINN/DirichletCuadrado.lean` y su import a `TesisPINN.lean`; se actualizó `MAPA_VERIFICACION.md`. No se cambiaron `Energia.lean`, `EnergiaSobolev.lean`, `LaplacianoDistribucional.lean` ni la tesis.

`lake env lean TesisPINN/DirichletCuadrado.lean` terminó con código 0. `lake build` terminó con código 0: **3173 trabajos**. Todos los `#print axioms` nuevos imprimieron solamente `propext`, `Classical.choice` y `Quot.sound`; ninguno imprimió `sorryAx`. No se introdujeron `sorry`, `admit` ni axiomas propios.

## Alcance por estado

**Completo para su enunciado Lean:** cuadrado abierto y acotado; suavidad del factor `ψ`; anulación de `ψ` cuando una coordenada está en `±1`; pertenencia a `H01` de `ψq` cuando `q` es una función de prueba con soporte compacto interior; caracterización de la aproximación en ambas componentes `L²`; especialización de la cota del Lema 3.19 al cuadrado.

**Compilado condicionalmente:** la cota (3.74) para grafos `h-u*`, pues requiere explícitamente `h-u*∈H01` y la igualdad distribucional `Δ(h-u*)=r`. Para dos candidatos `ψq` con `q` de soporte interior, `H01` ya se prueba; la identificación de `r` queda como premisa.

**Pendiente:** probar `ψq∈H01` para `q` suave no nula hasta la frontera; probar `h-u*∈H01` desde igualdad de trazas sin factorizar por `ψ`; construir el residuo `Δh-f` a partir de funciones concretas; obtener `Cₚ=√2/π`; formalizar la parte PINN y probabilística del Teorema 3.20. Las condiciones de frontera penalizadas no satisfacen por sí solas la premisa `H01`, por lo que la cota anterior no se aplica directamente.

El obstáculo analítico inmediato es un lema de recorte interior `χ_δ`: funciones suaves soportadas dentro del cuadrado, iguales a uno lejos de la frontera, con `‖∇χ_δ‖∞=O(1/δ)`. Para `ψq`, el valor del error en la franja es `O(δ)` si `q` es acotada; así se obtiene convergencia `L²` del error y de su gradiente. Para `h-u*` suave con frontera común, la misma cota se obtiene integrando el gradiente desde la frontera. El teorema `H1Graph.mem_H01_of_hasCompactSupport` de EllipticPDE resuelve la mollificación **después** de construir ese recorte, pero no cubre el soporte que toca la frontera.

