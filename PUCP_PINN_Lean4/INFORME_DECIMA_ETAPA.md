# Décima etapa: desigualdad integral de cobertura (3.13)

## Correspondencia con la tesis

Se cotejaron las páginas PDF 64–71 del Lema 3.5. La tesis parte de una red finita de radio `εr` en `U` y de radio `εb` en `Γ`, usa la desigualdad de tres sumandos con factor `3` en (3.14), integra sobre celdas de vecinos próximos y obtiene (3.13) con

`C_m = 3 max { C_r m_r ε_r^d, C_b m_b ε_b^(d−1) }`.

En esta formalización `d=2`, por lo que las potencias son `εr²` y `εb`. `ObjetivoCoberturaIntegral` reproduce el lado derecho de (3.13), incluidos los cuatro términos Hölder, los pesos residuales y el factor `3`. El código prueba `objetivoCoberturaIntegral_de_hipotesis`; el objetivo no figura entre sus premisas.

## Resultados compilados

- `VoronoiMedible.lean`: celdas con orden lexicográfico distancia–índice, cobertura de `U`, disjunción, mensurabilidad, inclusión en bolas cerradas y masa `μ(A_i) ≤ C ε^s`. El desempate funciona incluso si dos índices tienen la misma muestra.
- `CoberturaIntegral.lean`: integral sobre la partición, suma de masas igual a uno bajo concentración `μ(Uᶜ)=0`, versión indexada de (3.14), estimación integral de cada residuo, ensamblaje interior–frontera y fórmula exacta (3.13).
- `perdidaPoblacional_minimizador_bajo_cobertura`: cota determinista `LossPop(h_m) ≤ C_m a_m R* + 3 λr εr^(2α) Sf² + 3 λb εb^(2α) Sg²` bajo cobertura, comparador exacto, minimizador global y regularidad uniforme. Usa la comparación variacional, que conserva conjuntamente los términos de pérdida y regularización. Los lemas anteriores de cota empírica y de regularidad se especializan en la misma prueba, pero sus cotas separadas son más débiles para este ensamblaje.

La integrabilidad de los residuos al cuadrado y la concentración de las medidas en `U` y `Γ` figuran como hipótesis explícitas. `ProblemaPINN` por sí solo no las garantiza. También se exige que las muestras pertenezcan al dominio correspondiente y que las constantes de masa sean positivas. `CotasHolder` exige control Hölder de operadores y datos. La tesis usa `0<α≤1`; el argumento formal solo necesita `0<α`, por lo que es válido en particular bajo la hipótesis literal. Los residuos del proyecto son reales; la prueba vectorial general de (3.14) en el PDF no se declara formalizada.

## Verificación local

- `lean-toolchain`: Lean 4.35.0; `lakefile.toml`: Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.
- `lake build`: **exitoso, 3202 jobs**.
- `#print axioms` de los teoremas nuevos: únicamente `propext`, `Classical.choice`, `Quot.sound`; no aparece `sorryAx`.
- No se usaron `sorry`, `admit` ni axiomas nuevos.

## Alcance pendiente

La cota condicionada a cobertura no es (3.26). Faltan las probabilidades de ocupación del Lema 3.6 para muestras i.i.d., la elección de radios y escalas muestrales, y Borel–Cantelli para cobertura eventual casi segura. También falta derivar el control uniforme de (3.27)–(3.28). La implicación secundaria desde (3.4) hasta una cota esencial de `ρr` requiere diferenciación de Lebesgue, la identidad de medida con densidad y el volumen de bolas en `ℝ²`; no se necesitó para (3.13).

El PDF y los módulos Lean anteriores permanecieron intactos.
