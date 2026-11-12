# Etapa 21 · Proposición 3.15

Se usaron las páginas impresas 86–88 del PDF identificado por SHA-256 en el [inventario](INVENTARIO_FORMAL_CAPITULO_III.md). La base es la PR #22, commit `99223cb99ca288eb751832839499eaf474d83500`. Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`.

## Ley y constantes

| Dato de la tesis | Declaración Lean | Identidad o cota |
|---|---|---|
| Ley uniforme | `medidaUniformeCuadrado_apply`, `medidaUniformeCuadrado_concentrada`, `medidaUniformeCuadrado_densidad` | $\mu(A)=\operatorname{vol}(A\cap U)/4$ para $A$ medible. La instancia de probabilidad usa $\operatorname{vol}(U)=4$. |
| $c_r=1/9$, $D=\sqrt2$ | `particiones_uniformes_cuadrado` | Para $0<\eta\le1$, se usan $N=\lceil2/\eta\rceil$ celdas por lado, de longitud $\ell=2/N$. Cada celda contiene una caja abierta de masa $\ell^2/4\ge\eta^2/9$. La disjunción de las celdas semiabiertas es exacta y su unión es $U$. Su diámetro es a lo sumo $\sqrt2\eta$. |
| $C_r=\pi/4$ | `masa_bola_uniforme_cuadrado` | $\mu(U\cap\overline B(x,r))\le(\pi/4)r^2$. |
| $\kappa=3$, $s_m=\sqrt{27\log m/m}$, $\rho_m=\sqrt{54\log m/m}$ | `escalaAuxiliarLogCuadrado_eq`, `radioLogCuadrado_eq`, `radioLogCuadrado_admisible` | La escala auxiliar proviene del Lema 3.13 y el radio final multiplica por $\sqrt2$. Desde $m=310$ valen el radio final y los umbrales de escala y masa. |
| Umbral 310 | `signo_log_cuadrado_309`, `signo_log_cuadrado_310`, `monotona_diferencia_log_cuadrado` | Las cotas inferior y superior de la exponencial usan sumas de Taylor y aritmética racional. La desigualdad $\log t\le t-1$ da la monotonía desde 54. |
| $C_m=(81\pi/2)\log m$ | `factorLogInterior_eq` | $C_m=3C_rm\rho_m^2$. |
| $a_m=2\sqrt6/(9\pi\sqrt{m\log m})$ | `pesoLogInterior_eq`, `producto_pesoLogInterior` | $C_ma_m=3\rho_m$, pues $2\alpha=1$. |
| $1/(3m^2\log m)$ | `falloLogCuadrado_eq`, `ocupacion315` | Cota para el complemento del evento de ocupación. Intersectar con el soporte de todas las muestras conserva la cota. |

## Pérdida y energía

`ProblemaInterior` representa el promedio empírico interior, la pérdida de población y el funcional regularizado. Usa el ínfimo de las constantes Hölder no negativas de la restricción al dominio. Se demuestra que ese ínfimo es una constante Hölder y se aplica su cuadrado a $\Delta h$. La integrabilidad se deduce de las cotas Hölder, la acotación y la concentración de la ley. La cota determinista usa las celdas de Voronoi de la etapa anterior.

`proposicion315_perdida` establece (3.65) en un evento medible para todos los candidatos, y la cobertura eventual por el Lema 3.13. Para (3.66), las selecciones son funciones medibles del mismo prefijo. Se presuponen admisibilidad, comparador con pérdida $\le\tau_m$ y regularidad $\le R^*$, suboptimalidad aditiva $\delta_m$ respecto del ínfimo y $\tau_m+\delta_m\le K a_m$. La comparación usa `le_comparador_de_infimo` de `ComparadoresAproximados` y da $J_m(h_m)\le a_m(R^*+K)$ eventualmente. Se admite que las condiciones variacionales valgan eventualmente casi seguramente, suficiente para la tasa. (3.65) vale con cobertura por sí sola.

`proposicion315_poisson` toma el operador $\Delta(G+\psi q)$ y la clase de levantamiento suave con dato de Dirichlet $G|_{\partial U}$. `aproximacionLevantada_frontera` prueba la igualdad puntual en la frontera. La solución exacta es un grafo $H^1$ con $u^*-G\in H^1_0$ y $\Delta u^*=f$ en distribuciones. `dato315_memLp` obtiene el representante del dato a partir de Hölder. `perdidaPoissonInterior_eq_norma_residuo` prueba $E=\|\Delta h-f\|_{L^2(U)}^2/4$. El error $h-u^*$ pertenece a $H^1_0$ por `errorLevantado_mem_H01`; su laplaciano es $\Delta h-f$. La constante en `energia315_por_perdida` es $2\,\texttt{constanteEnergiaCuadrado}$ para todos los candidatos y realizaciones.

La ecuación (3.66) es la tasa de pérdida $O((\log m/m)^{1/2})$. La convergencia $H^1$ y la tasa $O((\log m/m)^{1/4})$ se deducen de ella en la clase con levantamiento suave. El lema `laplacianoLevantado_holder315` obtiene la regularidad Hölder de cada laplaciano suave a partir de una cota de su derivada sobre una bola compacta que contiene el cuadrado. La prueba probabilística de pérdida admite el laplaciano Hölder de una clase arbitraria, incluida la de la tesis al proveer su operador y selecciones. Extender el puente energético a toda la clase $C^{2,1/2}(\overline U)$ con traza exacta requiere el puente de traza o la aproximación por pruebas para esa clase. La existencia de comparadores, selecciones y arquitecturas concretas queda como hipótesis de instanciación.

## Verificación

El módulo raíz importa `Proposicion315`. Se ejecutaron `lake build` y las comprobaciones `#check` y `#print axioms`. Las declaraciones principales dependen de `propext`, `Classical.choice` y `Quot.sound`.

La ocupación se expresa mediante eventos medibles de celdas finitas. La conclusión asintótica usa `∀ᵐ` y la convergencia es de grafos $H^1$. Para la mensurabilidad del evento exacto se puede aplicar `prob_uno_convergenciaLevantada` cuando la aplicación a grafos sin levantamiento sea medible. La mensurabilidad de la pérdida como variable real requiere la de la evaluación conjunta del laplaciano con los datos.

## Reutilización para la Proposición 3.11

Ya están disponibles la ley y geometría interior, el funcional con exponente Hölder genérico, la cota de cobertura integral, la comparación aditiva con ínfimo y la transferencia energética de la pérdida. Queda instanciar la ocupación con el radio de raíz de la Proposición 3.11, verificar sus constantes y pesos, y ensamblar sus tasas $m^{-\alpha/2}$ y $m^{-\alpha/4}$ para el exponente original.
