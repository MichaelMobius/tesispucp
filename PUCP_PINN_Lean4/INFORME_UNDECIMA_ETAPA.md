# Undécima etapa: ocupación aleatoria y cobertura eventual

## Correspondencia con la tesis

El Lema 3.6 parte de una partición finita medible `X_k^η`, con celdas disjuntas, diámetro a lo sumo `√d η`, masa mínima `cη^s` y cardinal `Kη≤(cη^s)⁻¹`. Para `m` muestras i.i.d., la probabilidad de que una celda quede vacía es `(1−μ(X_k^η))^m`, y la de fallo de ocupación es a lo sumo `Kη exp(−mcη^s)`. La elección del texto es `t_m=√m`, `η=(t_m/(cm))^(1/s)=c^(-1/s)m^(-1/(2s))`, con fallo a lo sumo `√m exp(−√m)`. En dimensión dos se usa `s=2` en el interior y `s=1` en la frontera; el radio geométrico es `√2η` en ambos casos. Los tamaños `mr(n)` y `mb(n)` se tratan como funciones distintas.

El módulo `TesisPINN/OcupacionAleatoria.lean` demuestra exactamente la fórmula de celda vacía, su mensurabilidad, la cota exponencial, la desigualdad de la unión, la cota de cardinal bajo disjunción y masa mínima, la sumabilidad del mayorante para `m(n)≥n` eventualmente, y cobertura eventual casi segura mediante el primer lema de Borel–Cantelli. Las particiones y sus propiedades son datos explícitos, de acuerdo con la Hipótesis 3.2; no se supone medible el evento de cobertura definido por cuantificación sobre un dominio no numerable. El evento usado en Borel–Cantelli es una unión finita medible de fallos de ocupación.

`coberturas_cuadrado_eventuales_casi_seguras` reúne los eventos interiores y de frontera sobre el mismo espacio de probabilidad. Solo exige independencia i.i.d. dentro de cada secuencia. La intersección de dos eventos de probabilidad uno no precisa independencia entre secuencias.

`perdidaPoblacional_de_ocupacion` conecta la ocupación con `perdidaPoblacional_minimizador_bajo_cobertura`: si las muestras de `ProblemaPINN` son los prefijos realizados de las secuencias, la ocupación proporciona las dos hipótesis `MuestrasCubren`. Mantiene expresamente la concentración de medidas, la pertenencia de muestras a los dominios, las cotas Hölder, la integrabilidad poblacional, la minimalidad global, el comparador exacto, su regularidad uniforme y la elección de pesos. Es una desigualdad para una realización ocupada, no una afirmación casi segura sobre minimizadores aleatorios.

## Alcance y obstáculos pendientes

1. La Hipótesis 3.2 suministra celdas con masa inferior y diámetro controlado. La formalización no construye esas particiones a partir de una densidad concreta.
2. Para aplicar la cota superior de masa de bolas de (3.4) en `CoberturaIntegral`, todavía hay que demostrar eventualmente `ρr(n)≤εr₀` y `ρb(n)≤εb₀`. Son consecuencias analíticas esperables de `mr(n),mb(n)≥n` eventualmente y de las fórmulas de radio, pero aún no son lemas Lean en este proyecto.
3. La concentración de `μr` y `μb` en sus dominios debería implicar que todos los prefijos finitos de las muestras están allí casi seguramente. Esa transferencia de soporte no se ha integrado en un teorema final; el puente determinista conserva `hsr` y `hsb` como hipótesis visibles.
4. La Hipótesis 3.7 exige comparadores de interpolación exacta y regularidad uniforme sobre un evento de probabilidad uno; el Teorema 3.8 requiere minimizadores globales mensurables. Sus construcciones y las comprobaciones de integrabilidad no se han formalizado.
5. Para (3.26) falta combinar las afirmaciones eventuales anteriores con esos objetos aleatorios y probar la simplificación de `C_m a_m` bajo `mr=O(mb²)` para obtener `O(mr^(-α/2))`. La convergencia uniforme (3.27) y la tasa (3.28) requieren además la transferencia de pérdida a normas uniformes. No se afirma ninguna de las tres ecuaciones como teorema completo.

La elección `t_m=√m` no introduce logaritmos: `ηr` tiene orden `mr^(-1/4)` y `ηb` orden `mb^(-1/2)`; `C_m=3 max(Cr mr ρr²,Cb mb ρb)` conserva los factores y pesos definidos en la etapa anterior. Una elección alternativa `t_m≈log m` modificaría esas escalas y podría añadir logaritmos a la tasa; no se sustituye la elección de la tesis.

## Verificación

Versiones fijadas: Lean `v4.35.0`, Mathlib `v4.35.0`, EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. El nuevo módulo no contiene `sorry`, `admit` ni declaraciones de axiomas. Las salidas de `#print axioms` para sus teoremas muestran solo `propext`, `Classical.choice` y `Quot.sound`.

`lake build` local terminó correctamente: **3223 trabajos**. La compilación de `TesisPINN/OcupacionAleatoria.lean` y su importación desde `TesisPINN.lean` pasaron. El CI «Lean 4 / Mathlib» de la [PR #13](https://github.com/MichaelMobius/tesispucp/pull/13) concluyó con éxito en la [ejecución 42668983809](https://github.com/MichaelMobius/tesispucp/actions/runs/42668983809).
