# Etapa 22 · Proposición 3.11

Se cotejaron las páginas impresas 77–80 del PDF normativo identificado en el [inventario](INVENTARIO_FORMAL_CAPITULO_III.md). La base Lean es la PR #23, commit `1da91cf7fb759e143b3549ef2e96dda4729fe2b7`.

## Correspondencia con el enunciado

| Ecuación | Declaración Lean | Correspondencia |
|---|---|---|
| (3.44) | `perdidaEmpiricaInterior`, `perdidaPoissonInterior_eq` | El promedio se toma sobre el mismo prefijo que usa la ocupación. $E(h)=\tfrac14\int_U|\Delta h-f|^2\,dx$. |
| (3.45) | `seminormaInterior_cota`, `funcional311` | Se usa el ínfimo de las constantes Hölder de la restricción a $U$, al cuadrado. En la instancia de Poisson el operador es el laplaciano clásico. La condición de frontera está incorporada en la clase. |
| (3.46) | `radioRaizCuadrado_eq`, `radioRaizCuadrado_le_uno_iff` | $\rho_m=3\sqrt2\,m^{-1/4}$ para $m>0$. El radio es a lo sumo uno exactamente cuando $m\ge324$. |
| (3.47) | `factorRaizInterior_eq` | $C_m=3(\pi/4)m\rho_m^2=(27\pi/2)\sqrt m$. |
| (3.48) | `pesoRaizInterior`, `producto_pesoRaizInterior`, `pesoRaizInterior_eq_potencia` | $a_m=3\rho_m^{2\alpha}/C_m$, con $C_ma_m=3\rho_m^{2\alpha}$ y $a_m=[3(3\sqrt2)^{2\alpha}/(27\pi/2)]m^{-(\alpha+1)/2}$. |
| (3.49) | `ocupacion311`, `evento311` | $\mathbb P(\Omega_m^{\mathrm{int}})\ge1-\sqrt m(1-1/\sqrt m)^m$. El evento es preimagen de un conjunto medible de prefijos. |
| (3.50) | `perdida311_bajo_cobertura`, `evento311` | $E(h)\le C_m J_m(h)+3\rho_m^{2\alpha}[f]_{\alpha;U}^2$ simultáneamente para todos los admisibles. |
| (3.51) | `Selecciones311` | Contiene admisibilidad, $E_m(v_m)\le\eta_m$, $R(v_m)\le R^*$ y $J_m(h_m)\le\inf_{v\in\mathcal H_m^0}J_m(v)+\delta_m$. Las dos tolerancias y $R^*$ son deterministas. |
| (3.52)–(3.53) | `cotas311`, `Resultados311.cotas` | Con $\kappa_m=(\eta_m+\delta_m)/a_m$ se obtienen $R(h_m)\le R^*+\kappa_m$ y $J_m(h_m)\le a_m(R^*+\kappa_m)$. La sustitución bajo cobertura da (3.53). |
| (3.54) | `pesoRaizInterior_medio`, `proposicion311_perdida` | Para $\alpha=1/2$, $a_m=(2\sqrt2/(3\pi))m^{-3/4}$ y $E(h_m)=O(m^{-1/4})$ casi seguramente. |
| (3.55) | `proposicion311_poisson`, `escalaEnergia311_eq` | En la clase levantada se obtiene convergencia en $H^1$ y tasa $O(m^{-\alpha/4})$. El exponente del PDF para $\alpha=1/2$ es $1/8$. |

La geometría usa la ley de densidad $1/4$ respecto del volumen restringido, $c_r=1/9$, $C_r=\pi/4$ y la partición semiabierta exactamente disjunta ya verificada. Para $m\ge324$ también se obtienen $0<\eta\le1$ para la escala auxiliar y $0<1/\sqrt m\le1$ para la masa mínima. La cota binomial se deduce de la fórmula de celda vacía y el máximo de $\sqrt m$ celdas que permite la masa mínima. Borel–Cantelli usa la serie de $\sqrt m\exp(-\sqrt m)$ mediante `cobertura_eventual_de_particiones_raiz`. La intersección con la condición de que el prefijo esté en $U$ conserva la cota de probabilidad por concentración. No se exige independencia entre prefijos.

La tasa se aplica a cualquier sucesión $m(n)\to\infty$ con $\eta_{m(n)}+\delta_{m(n)}\le K a_{m(n)}$ eventualmente. La cobertura se obtiene primero para todos los tamaños enteros suficientemente grandes, lo que permite restringirla después a $m(n)$. Las cotas finitas (3.52)–(3.53) preceden a la condición eventual de tolerancias.

## Alcance de la instancia de Poisson

`proposicion311_perdida` se enuncia para una clase abstracta con operador escalar Hölder en $U$. La regularidad de la tesis sobre $\overline U$ proporciona el control requerido en el interior. La clase concreta en `proposicion311_poisson` usa $h=G+\psi q$ con $G,q$ globalmente suaves. `aproximacionLevantada_frontera` prueba la igualdad de valores con $G$ en toda la frontera, y `errorLevantado_mem_H01` usa la condición $u^*-G\in H^1_0(U)$. La ecuación distribucional del error es $\Delta(h-u^*)=\Delta h-f$ por `laplaciano_errorLevantado`. La normalización da $E(h)=\|\Delta h-f\|_{L^2(U)}^2/4$ y la constante de transferencia es $2\,\texttt{constanteEnergiaCuadrado}$, independiente de la realización y del tamaño.

La extensión energética a toda la clase $C^{2,\alpha}(\overline U)\cap H^1(U)$ con la traza prescrita sigue pendiente del puente de trazas. La solución exacta, las selecciones y sus desigualdades variacionales figuran como premisas. Se representan ambos selectores como funciones medibles del prefijo, una formulación explícita de su dependencia muestral. La prueba se expresa mediante `∀ᵐ`. Para medir la pérdida como variable real se necesita mensurabilidad conjunta de la evaluación del laplaciano. La mensurabilidad del evento exacto de convergencia en $H^1$ se puede obtener mediante `prob_uno_convergenciaLevantada` cuando el selector seguido del mapa al grafo homogéneo sea medible.

## Continuidad

1. El Lema 3.17 es la siguiente dependencia directa. Fijar el operador elíptico, verificar la barrera exponencial y formalizar el máximo débil con las hipótesis de regularidad y signo de la tesis.
2. Para el Teorema 3.18, aplicar esa cota a la diferencia con una solución clásica dada y transferir los dos controles uniformes de `teorema38_dim2`. La existencia clásica y la geometría de esfera exterior se auditan por separado.
3. Mantener en paralelo la ruta de comparadores. Hermite exige Vandermonde confluente, tratamiento boreliano de colisiones y resto $C^3$ uniforme. Taylor exige extensión entera, cotas de Cauchy y resto diferenciado del producto tensorial. Ambos alimentan el criterio de tolerancias de C3.12 y las tasas de P3.11/P3.15. La realización de esos polinomios por la red cuadrática de L3.24 y la selección de mínimos de C3.26 completan la instancia neuronal.
