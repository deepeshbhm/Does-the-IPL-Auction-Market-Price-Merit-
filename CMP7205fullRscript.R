# =============================================================================
# CMP7205 APPLIED STATISTICS - COURSEWORK ANALYSIS
# Does the Auction Market Price Merit? A Statistical Analysis of IPL Auction
# Prices and Player Performance, 2013 to 2022
# =============================================================================
#
# This script runs the full analysis end to end: from the three raw input
# files through to every table and figure reported in the coursework report.
#
# REQUIRED INPUT FILES (place in the working directory):
#   - matches.csv              (IPL Complete Dataset, patrickb1912, Kaggle)
#   - deliveries.csv           (IPL Complete Dataset, patrickb1912, Kaggle)
#   - IPLPlayerAuctionData.csv (IPL Player Auction Dataset, kalilurrahman, Kaggle)
#
# REQUIRED PACKAGES (all available via CRAN or your distribution's r-cran-*
# packages, e.g. `sudo apt install r-cran-dplyr r-cran-tidyr r-cran-stringr
# r-cran-ggplot2 r-cran-e1071 r-cran-car r-cran-broom r-cran-effectsize
# r-cran-metrics` on Ubuntu/Debian, or install.packages(...) elsewhere):

library(dplyr)
library(tidyr)
library(stringr)
library(ggplot2)
library(e1071)        # skewness()
library(car)           # Levene's test, VIF
library(effectsize)      # rank_biserial()
library(broom)             # tidy regression output
library(Metrics)              # rmse(), mae()

# FSA (Dunn's post-hoc test) is optional: it is only invoked if RQ4's
# Kruskal-Wallis test comes back significant, which it does not for this
# dataset. If you have FSA installed, the post-hoc branch will run
# automatically; if not, the script prints a note and continues.
has_FSA <- requireNamespace("FSA", quietly = TRUE)

# A small local replacement for ggcorrplot(), avoiding a dependency that is
# not always available: builds an equivalent lower-triangle correlation
# heatmap directly from ggplot2.
plot_corr_heatmap <- function(corr_matrix, title, low_col = "firebrick", high_col = "steelblue") {
  corr_df <- as.data.frame(as.table(corr_matrix))
  names(corr_df) <- c("Var1", "Var2", "value")
  # keep only the lower triangle (var1 appears after var2 in the matrix order)
  ord <- rownames(corr_matrix)
  corr_df <- corr_df %>%
    mutate(Var1 = factor(Var1, levels = ord), Var2 = factor(Var2, levels = ord)) %>%
    filter(as.integer(Var1) > as.integer(Var2))
  ggplot(corr_df, aes(x = Var2, y = Var1, fill = value)) +
    geom_tile(colour = "white") +
    geom_text(aes(label = sprintf("%.2f", value)), size = 4) +
    scale_fill_gradient2(low = low_col, mid = "white", high = high_col,
                          midpoint = 0, limits = c(-1, 1), name = "Corr") +
    labs(title = title, x = NULL, y = NULL) +
    theme_minimal() +
    theme(axis.text.x = element_text(angle = 45, hjust = 1))
}

set.seed(42)

# Set this to the folder containing the three CSV files before running.
# setwd("path/to/your/data")


# =============================================================================
# SECTION 0: LOAD RAW DATA
# =============================================================================

matches    <- read.csv("matches.csv", stringsAsFactors = FALSE, fileEncoding = "UTF-8-BOM")
deliveries <- read.csv("deliveries.csv", stringsAsFactors = FALSE, fileEncoding = "UTF-8-BOM")
auction    <- read.csv("IPLPlayerAuctionData.csv", stringsAsFactors = FALSE, fileEncoding = "UTF-8-BOM")
names(auction)[names(auction) == "Player.Origin"] <- "Player_Origin"

cat(sprintf("Loaded: %d matches, %d deliveries, %d auction records (%d unique players)\n",
            nrow(matches), nrow(deliveries), nrow(auction), n_distinct(auction$Player)))


# =============================================================================
# SECTION 1: DATA PREPARATION (RQ1 groundwork; Section 3.1 of the report)
# =============================================================================
# Builds season-level batting/bowling performance metrics from ball-by-ball
# data, then links auction records to those metrics using a three-tier name-
# matching procedure (exact match -> fuzzy match -> manual correction).

## -- 1.1 Attach season to each delivery, build a season-year lookup ---------
match_season <- matches %>% select(id, season)
deliveries <- deliveries %>% left_join(match_season, by = c("match_id" = "id"))
matches <- matches %>% mutate(season_year = as.numeric(substr(season, 1, 4)))
season_lookup <- matches %>% distinct(season, season_year)

## -- 1.2 Season-level batting metrics ----------------------------------------
# Balls faced excludes wides (not a legal delivery faced by the batter).
batting_stats <- deliveries %>%
  filter(is.na(extras_type) | extras_type != "wides") %>%
  group_by(batter, season) %>%
  summarise(
    runs        = sum(batsman_runs, na.rm = TRUE),
    balls_faced = n(),
    dismissals  = sum(is_wicket == 1 & player_dismissed == batter, na.rm = TRUE),
    .groups = "drop"
  ) %>%
  mutate(
    strike_rate = ifelse(balls_faced > 0, round(runs / balls_faced * 100, 2), NA),
    batting_avg = ifelse(dismissals > 0, round(runs / dismissals, 2), NA)
  ) %>%
  rename(player = batter) %>%
  left_join(season_lookup, by = "season")

## -- 1.3 Season-level bowling metrics -----------------------------------------
# Legal deliveries exclude wides and no-balls (not over-balls for the bowler),
# but runs off them ARE charged to the bowler, except byes/leg-byes, which
# are NOT charged to the bowler. Run-outs are not credited as bowler wickets.
bowling_stats <- deliveries %>%
  mutate(
    legal_ball   = !(extras_type %in% c("wides", "noballs")),
    runs_charged = ifelse(extras_type %in% c("byes", "legbyes"), 0, total_runs)
  ) %>%
  group_by(bowler, season) %>%
  summarise(
    balls_bowled  = sum(legal_ball, na.rm = TRUE),
    runs_conceded = sum(runs_charged, na.rm = TRUE),
    wickets       = sum(is_wicket == 1 &
                         !(dismissal_kind %in% c("run out", "retired hurt",
                                                  "obstructing the field")),
                         na.rm = TRUE),
    .groups = "drop"
  ) %>%
  mutate(
    overs_bowled = round(balls_bowled / 6, 1),
    economy_rate = ifelse(balls_bowled > 0,
                           round(runs_conceded / (balls_bowled / 6), 2), NA)
  ) %>%
  rename(player = bowler) %>%
  left_join(season_lookup, by = "season")

## -- 1.4 Three-tier player name matching --------------------------------------
# Auction data uses full names ("Kieron Pollard"); match data uses scorecard
# convention ("KA Pollard"). No shared identifier exists across the two
# sources.
make_key <- function(name) {
  clean <- str_replace_all(str_trim(name), "\\.", "")
  parts <- str_split(clean, "\\s+")[[1]]
  if (length(parts) < 2) return(NA)
  initial <- tolower(substr(parts[1], 1, 1))
  surname <- tolower(parts[length(parts)])
  paste(initial, surname, sep = "_")
}

perf_players <- unique(c(batting_stats$player, bowling_stats$player))
perf_key_df <- data.frame(
  perf_name = perf_players,
  match_key = sapply(perf_players, make_key),
  stringsAsFactors = FALSE
)
perf_key_counts <- perf_key_df %>% count(match_key)
unique_perf_keys <- perf_key_counts$match_key[perf_key_counts$n == 1]
key_lookup <- perf_key_df %>% filter(match_key %in% unique_perf_keys)

# Tier 3: manual overrides for high-value players whose auction name uses a
# different naming convention entirely (identified by inspecting the highest-
# value unmatched records after tiers 1-2).
manual_overrides <- c(
  "Dinesh Karthik"     = "KD Karthik",
  "Prasidh Krishna"    = "M Prasidh Krishna",
  "Rashid Khan Arman"  = "Rashid Khan",
  "Praveen Kumar"      = "P Kumar"
)

auction_players <- auction %>%
  distinct(Player) %>%
  rowwise() %>%
  mutate(
    exact_match = ifelse(Player %in% perf_players, Player, NA),  # Tier 1
    match_key   = make_key(Player)
  ) %>%
  ungroup() %>%
  left_join(key_lookup %>% select(match_key, fuzzy_match = perf_name),
            by = "match_key") %>%                                 # Tier 2
  mutate(
    manual_match = manual_overrides[Player],                      # Tier 3
    perf_name = coalesce(exact_match, fuzzy_match, manual_match)
  )

n_matched <- sum(!is.na(auction_players$perf_name))
cat(sprintf("\nPlayer name matching: %d of %d unique auction players matched (%.1f%%)\n",
            n_matched, nrow(auction_players), n_matched / nrow(auction_players) * 100))

player_lookup <- auction_players %>%
  filter(!is.na(perf_name)) %>%
  select(Player, perf_name)

auction_matched <- auction %>% inner_join(player_lookup, by = "Player")

unmatched <- auction_players %>%
  filter(is.na(perf_name)) %>%
  select(Player) %>%
  left_join(auction %>% group_by(Player) %>% summarise(max_amount = max(Amount)),
            by = "Player") %>%
  arrange(desc(max_amount))
write.csv(unmatched, "unmatched_auction_players.csv", row.names = FALSE)

## -- 1.5 Join auction records to NEXT-season performance (predictive) --------
# Deliberate design choice: price(Year) is joined to performance(Year+1), not
# the same season, to avoid reverse causality when testing whether price
# PREDICTS future performance (RQ2).
auction_matched <- auction_matched %>% mutate(target_season_year = Year + 1)

batting_next <- auction_matched %>%
  left_join(batting_stats, by = c("perf_name" = "player", "target_season_year" = "season_year"))

bowling_next <- auction_matched %>%
  left_join(bowling_stats, by = c("perf_name" = "player", "target_season_year" = "season_year"))

write.csv(batting_next, "merged_batting_price_performance.csv", row.names = FALSE)
write.csv(bowling_next, "merged_bowling_price_performance.csv", row.names = FALSE)

cat(sprintf("Batting rows with next-season data: %d | Bowling rows: %d\n",
            sum(!is.na(batting_next$runs)), sum(!is.na(bowling_next$wickets))))


# =============================================================================
# SECTION 2: RQ1 - DISTRIBUTION AND NORMALITY
# =============================================================================

cat("\n================ RQ1: Distribution and Normality ================\n")

cat("\n--- Auction price: overall summary ---\n")
print(summary(auction$Amount))
cat(sprintf("SD: %.0f | Skewness: %.2f\n",
            sd(auction$Amount, na.rm = TRUE), skewness(auction$Amount, na.rm = TRUE)))

cat("\n--- Auction price by Role (Table 1) ---\n")
auction %>% group_by(Role) %>%
  summarise(n = n(), mean = mean(Amount), median = median(Amount),
            sd = sd(Amount), skew = skewness(Amount)) %>% print()

cat("\n--- Auction price by Player Origin (Table 2) ---\n")
auction %>% group_by(Player_Origin) %>%
  summarise(n = n(), mean = mean(Amount), median = median(Amount),
            sd = sd(Amount), skew = skewness(Amount)) %>% print()

# Figures 1-3: price distribution and by-group boxplots
ggsave("fig1_price_histogram.png",
       ggplot(auction, aes(x = Amount)) +
         geom_histogram(bins = 40, fill = "steelblue", colour = "white") +
         labs(title = "Distribution of IPL Auction Prices", x = "Auction Price (INR)", y = "Count") +
         theme_minimal(), width = 7, height = 5)

ggsave("fig2_price_by_role_boxplot.png",
       ggplot(auction, aes(x = Role, y = Amount, fill = Role)) + geom_boxplot() +
         labs(title = "Auction Price by Player Role", x = "Role", y = "Auction Price (INR)") +
         theme_minimal() + theme(legend.position = "none"), width = 7, height = 5)

ggsave("fig3_price_by_origin_boxplot.png",
       ggplot(auction, aes(x = Player_Origin, y = Amount, fill = Player_Origin)) + geom_boxplot() +
         labs(title = "Auction Price by Player Origin", x = "Origin", y = "Auction Price (INR)") +
         theme_minimal() + theme(legend.position = "none"), width = 7, height = 5)

# Figures 4-5: performance metric distributions (next-season, pre-threshold)
ggsave("fig4_strike_rate_histogram.png",
       ggplot(batting_next %>% filter(!is.na(strike_rate)), aes(x = strike_rate)) +
         geom_histogram(bins = 40, fill = "darkorange", colour = "white") +
         labs(title = "Distribution of Batting Strike Rate (next season)", x = "Strike Rate", y = "Count") +
         theme_minimal(), width = 7, height = 5)

ggsave("fig5_economy_rate_histogram.png",
       ggplot(bowling_next %>% filter(!is.na(economy_rate)), aes(x = economy_rate)) +
         geom_histogram(bins = 40, fill = "seagreen", colour = "white") +
         labs(title = "Distribution of Bowling Economy Rate (next season)", x = "Economy Rate", y = "Count") +
         theme_minimal(), width = 7, height = 5)

# Table 3: Shapiro-Wilk normality tests
cat("\n--- Shapiro-Wilk normality tests (Table 3) ---\n")
sw_price <- shapiro.test(auction$Amount)
sw_sr    <- shapiro.test(batting_next$strike_rate[!is.na(batting_next$strike_rate)])
sw_econ  <- shapiro.test(bowling_next$economy_rate[!is.na(bowling_next$economy_rate)])
cat(sprintf("Auction Price:  W = %.4f, p = %.4g\n", sw_price$statistic, sw_price$p.value))
cat(sprintf("Strike Rate:    W = %.4f, p = %.4g\n", sw_sr$statistic, sw_sr$p.value))
cat(sprintf("Economy Rate:   W = %.4f, p = %.4g\n", sw_econ$statistic, sw_econ$p.value))

# Figure 6: Q-Q plot
png("fig6_price_qqplot.png", width = 600, height = 500)
qqnorm(auction$Amount, main = "Q-Q Plot: Auction Price"); qqline(auction$Amount, col = "red")
dev.off()

# Table 4: IQR outlier detection -- flag carries through into every later join
q1 <- quantile(auction$Amount, 0.25); q3 <- quantile(auction$Amount, 0.75)
iqr <- q3 - q1
lower_bound <- q1 - 1.5 * iqr; upper_bound <- q3 + 1.5 * iqr
auction <- auction %>% mutate(price_outlier = Amount < lower_bound | Amount > upper_bound)
cat(sprintf("\n--- Outlier detection (Table 4) ---\nBounds: [%.0f, %.0f] | Outliers: %d of %d (%.1f%%)\n",
            lower_bound, upper_bound, sum(auction$price_outlier), nrow(auction),
            mean(auction$price_outlier) * 100))

# Propagate the outlier flag through the matched/joined datasets
auction_matched <- auction_matched %>%
  left_join(auction %>% select(Player, Year, Amount, price_outlier), by = c("Player", "Year", "Amount"))
batting_next <- batting_next %>%
  left_join(auction %>% select(Player, Year, Amount, price_outlier), by = c("Player", "Year", "Amount"))
bowling_next <- bowling_next %>%
  left_join(auction %>% select(Player, Year, Amount, price_outlier), by = c("Player", "Year", "Amount"))


# =============================================================================
# SECTION 3: RQ2 - CORRELATION BETWEEN PRICE AND PERFORMANCE
# =============================================================================

cat("\n================ RQ2: Correlation ================\n")

# Minimum-sample thresholds (Section 3.1): remove noisy small-sample metrics
batting_clean <- batting_next %>% filter(!is.na(runs), balls_faced >= 10)
bowling_clean <- bowling_next %>% filter(!is.na(wickets), overs_bowled >= 3)
cat(sprintf("Batting rows after threshold: %d (was %d)\n", nrow(batting_clean), sum(!is.na(batting_next$runs))))
cat(sprintf("Bowling rows after threshold: %d (was %d)\n", nrow(bowling_clean), sum(!is.na(bowling_next$wickets))))

run_correlation <- function(x, y, label) {
  p <- cor.test(x, y, method = "pearson")
  s <- cor.test(x, y, method = "spearman", exact = FALSE)
  cat(sprintf("%-30s Pearson r = %6.3f (p = %.4g)   Spearman rho = %6.3f (p = %.4g)\n",
              label, p$estimate, p$p.value, s$estimate, s$p.value))
}

cat("\n--- Table 5: Price vs next-season performance ---\n")
run_correlation(batting_clean$Amount, batting_clean$strike_rate, "Price vs Strike Rate")
run_correlation(batting_clean$Amount, batting_clean$runs,        "Price vs Runs")
ba <- batting_clean %>% filter(!is.na(batting_avg))
run_correlation(ba$Amount, ba$batting_avg, "Price vs Batting Average")
run_correlation(bowling_clean$Amount, bowling_clean$economy_rate, "Price vs Economy Rate")
run_correlation(bowling_clean$Amount, bowling_clean$wickets,      "Price vs Wickets")

# Figures 7-8: correlation heatmaps
bat_corr <- cor(batting_clean %>% select(Amount, strike_rate, runs, batting_avg) %>% na.omit(), method = "spearman")
ggsave("fig7_batting_correlation_heatmap.png",
       plot_corr_heatmap(bat_corr, "Correlation Matrix: Price & Batting Metrics (Spearman)"),
       width = 6, height = 6)

bowl_corr <- cor(bowling_clean %>% select(Amount, economy_rate, wickets, runs_conceded) %>% na.omit(), method = "spearman")
ggsave("fig8_bowling_correlation_heatmap.png",
       plot_corr_heatmap(bowl_corr, "Correlation Matrix: Price & Bowling Metrics (Spearman)", high_col = "seagreen"),
       width = 6, height = 6)

# Figure 9: scatter with fitted trend
ggsave("fig9_price_vs_strikerate_scatter.png",
       ggplot(batting_clean, aes(x = Amount, y = strike_rate)) +
         geom_point(alpha = 0.5, colour = "steelblue") +
         geom_smooth(method = "lm", se = TRUE, colour = "firebrick") +
         labs(title = "Auction Price vs Next-Season Strike Rate", x = "Auction Price (INR)", y = "Strike Rate") +
         theme_minimal(), width = 7, height = 5)

# Table 6: outlier sensitivity
cat("\n--- Table 6: Outlier sensitivity ---\n")
bat_wo <- batting_clean %>% filter(price_outlier == FALSE | is.na(price_outlier))
bowl_wo <- bowling_clean %>% filter(price_outlier == FALSE | is.na(price_outlier))
cat("Price vs Strike Rate, WITH outliers:\n");    run_correlation(batting_clean$Amount, batting_clean$strike_rate, "  ")
cat("Price vs Strike Rate, WITHOUT outliers:\n"); run_correlation(bat_wo$Amount, bat_wo$strike_rate, "  ")
cat("Price vs Economy Rate, WITH outliers:\n");    run_correlation(bowling_clean$Amount, bowling_clean$economy_rate, "  ")
cat("Price vs Economy Rate, WITHOUT outliers:\n"); run_correlation(bowl_wo$Amount, bowl_wo$economy_rate, "  ")


# =============================================================================
# SECTION 4: RQ2 EXTENSION - RETROSPECTIVE VS PREDICTIVE VALIDITY
# =============================================================================
# Re-joins the SAME matched auction records to the PRIOR season's performance
# (Year - 1) instead of the next season, to compare retrospective pricing
# accuracy against predictive validity.

cat("\n================ RQ2 Extension: Retrospective vs Predictive ================\n")

auction_matched <- auction_matched %>% mutate(prior_season_year = Year - 1)

batting_prior <- auction_matched %>%
  left_join(batting_stats, by = c("perf_name" = "player", "prior_season_year" = "season_year")) %>%
  filter(!is.na(runs), balls_faced >= 10)

bowling_prior <- auction_matched %>%
  left_join(bowling_stats, by = c("perf_name" = "player", "prior_season_year" = "season_year")) %>%
  filter(!is.na(wickets), overs_bowled >= 3)

cat(sprintf("Prior-season batting sample: N = %d | bowling: N = %d\n",
            nrow(batting_prior), nrow(bowling_prior)))

cat("\n--- Table 7: Retrospective (prior-season) validity ---\n")
run_correlation(batting_prior$Amount, batting_prior$strike_rate, "Price vs Prior Strike Rate")
run_correlation(batting_prior$Amount, batting_prior$runs,        "Price vs Prior Runs")
run_correlation(bowling_prior$Amount, bowling_prior$economy_rate,"Price vs Prior Economy Rate")
run_correlation(bowling_prior$Amount, bowling_prior$wickets,     "Price vs Prior Wickets")

# Figure 10: retrospective vs predictive comparison
comparison_df <- data.frame(
  metric = rep(c("Strike Rate", "Runs", "Economy Rate", "Wickets"), 2),
  direction = rep(c("Retrospective (prior season)", "Predictive (next season)"), each = 4),
  spearman_rho = c(
    cor(batting_prior$Amount, batting_prior$strike_rate, method = "spearman"),
    cor(batting_prior$Amount, batting_prior$runs, method = "spearman"),
    cor(bowling_prior$Amount, bowling_prior$economy_rate, method = "spearman"),
    cor(bowling_prior$Amount, bowling_prior$wickets, method = "spearman"),
    cor(batting_clean$Amount, batting_clean$strike_rate, method = "spearman"),
    cor(batting_clean$Amount, batting_clean$runs, method = "spearman"),
    cor(bowling_clean$Amount, bowling_clean$economy_rate, method = "spearman"),
    cor(bowling_clean$Amount, bowling_clean$wickets, method = "spearman")
  )
)
ggsave("fig10_retrospective_vs_predictive.png",
       ggplot(comparison_df, aes(x = metric, y = spearman_rho, fill = direction)) +
         geom_col(position = "dodge") + geom_hline(yintercept = 0, colour = "grey40") +
         labs(title = "Retrospective vs Predictive Validity of Auction Price",
              subtitle = "Spearman's rho: price correlates more with PAST than FUTURE performance",
              x = NULL, y = "Spearman's rho", fill = NULL) +
         theme_minimal() + theme(legend.position = "bottom"), width = 7, height = 5)


# =============================================================================
# SECTION 5: RQ3 - AUCTION PRICE BY PLAYER ORIGIN
# =============================================================================
# Uses the FULL auction dataset (970 rows), not the performance-matched
# subset, since this question concerns price alone.

cat("\n================ RQ3: Price by Player Origin ================\n")

lev3 <- leveneTest(Amount ~ Player_Origin, data = auction)
cat(sprintf("Levene's test: F = %.3f, p = %.4g\n", lev3$`F value`[1], lev3$`Pr(>F)`[1]))

mw <- wilcox.test(Amount ~ Player_Origin, data = auction, conf.int = TRUE)
cat(sprintf("Mann-Whitney U: W = %.0f, p = %.4g\n", mw$statistic, mw$p.value))

cat("\n--- Table 8: medians by origin ---\n")
auction %>% group_by(Player_Origin) %>% summarise(median_price = median(Amount), n = n()) %>% print()

eff3 <- rank_biserial(Amount ~ Player_Origin, data = auction)
cat(sprintf("Rank-biserial r = %.3f\n", eff3$r_rank_biserial))

ggsave("fig11_rq3_origin_boxplot.png",
       ggplot(auction, aes(x = Player_Origin, y = Amount, fill = Player_Origin)) + geom_boxplot() +
         labs(title = "RQ3: Auction Price by Player Origin",
              subtitle = sprintf("Mann-Whitney U, p = %.4g", mw$p.value),
              x = "Origin", y = "Auction Price (INR)") +
         theme_minimal() + theme(legend.position = "none"), width = 6, height = 5)


# =============================================================================
# SECTION 6: RQ4 - AUCTION PRICE BY PLAYING ROLE
# =============================================================================

cat("\n================ RQ4: Price by Playing Role ================\n")

lev4 <- leveneTest(Amount ~ as.factor(Role), data = auction)
cat(sprintf("Levene's test: F = %.3f, p = %.4g\n", lev4$`F value`[1], lev4$`Pr(>F)`[1]))

kw <- kruskal.test(Amount ~ as.factor(Role), data = auction)
cat(sprintf("Kruskal-Wallis: H(%d) = %.3f, p = %.4g\n", kw$parameter, kw$statistic, kw$p.value))

if (kw$p.value < 0.05) {
  if (has_FSA) {
    cat("Significant -> running Dunn's post-hoc test:\n")
    print(FSA::dunnTest(Amount ~ as.factor(Role), data = auction, method = "bonferroni")$res)
  } else {
    cat("Significant, but FSA is not installed -> install FSA to run Dunn's post-hoc test.\n")
  }
} else {
  cat("Not significant at alpha = .05 -> no post-hoc test run (Table 9).\n")
}

cat("\n--- Table 9: medians by role ---\n")
auction %>% group_by(Role) %>%
  summarise(median_price = median(Amount), mean_price = mean(Amount), n = n()) %>% print()

ggsave("fig12_rq4_role_boxplot.png",
       ggplot(auction, aes(x = Role, y = Amount, fill = Role)) + geom_boxplot() +
         labs(title = "RQ4: Auction Price by Role",
              subtitle = sprintf("Kruskal-Wallis, p = %.4g (not significant)", kw$p.value),
              x = "Role", y = "Auction Price (INR)") +
         theme_minimal() + theme(legend.position = "none"), width = 6, height = 5)


# =============================================================================
# SECTION 7: RQ5 - PREDICTING PRICE FROM PERFORMANCE (REGRESSION)
# =============================================================================

cat("\n================ RQ5: Regression ================\n")

sw_raw <- shapiro.test(batting_clean$Amount)
sw_log <- shapiro.test(log(batting_clean$Amount))
cat(sprintf("Raw price:  W = %.4f, p = %.4g | Log price: W = %.4f, p = %.4g\n",
            sw_raw$statistic, sw_raw$p.value, sw_log$statistic, sw_log$p.value))

## -- 7.1 Batting model --------------------------------------------------------
bat_df <- batting_clean %>%
  filter(!is.na(strike_rate), !is.na(runs), !is.na(Role), !is.na(Player_Origin)) %>%
  mutate(log_price = log(Amount))

model_bat <- lm(log_price ~ strike_rate + runs + Role + Player_Origin, data = bat_df)
cat("\n--- Table 10: Batting regression ---\n")
print(summary(model_bat))
print(tidy(model_bat, conf.int = TRUE), n = Inf)
cat("\nVIF:\n"); print(vif(model_bat))

ggsave("fig13_batting_regression_coefficients.png",
       ggplot(tidy(model_bat, conf.int = TRUE) %>% filter(term != "(Intercept)"),
              aes(x = reorder(term, estimate), y = estimate)) +
         geom_point(size = 3, colour = "steelblue") +
         geom_errorbar(aes(ymin = conf.low, ymax = conf.high), width = 0.2) +
         geom_hline(yintercept = 0, linetype = "dashed", colour = "red") + coord_flip() +
         labs(title = "RQ5: Batting Regression Coefficients for Log(Auction Price)",
              x = NULL, y = "Coefficient (log price scale)") + theme_minimal(),
       width = 7, height = 5)

png("fig14_batting_residuals_vs_fitted.png", width = 600, height = 500); plot(model_bat, which = 1); dev.off()
png("fig15_batting_residuals_qqplot.png", width = 600, height = 500); plot(model_bat, which = 2); dev.off()
png("fig16_batting_scale_location.png", width = 600, height = 500); plot(model_bat, which = 3); dev.off()

## -- 7.2 Bowling model --------------------------------------------------------
bowl_df <- bowling_clean %>%
  filter(!is.na(economy_rate), !is.na(wickets), !is.na(Role), !is.na(Player_Origin)) %>%
  mutate(log_price = log(Amount))

model_bowl <- lm(log_price ~ economy_rate + wickets + Role + Player_Origin, data = bowl_df)
cat("\n--- Table 11: Bowling regression ---\n")
print(summary(model_bowl))
print(tidy(model_bowl, conf.int = TRUE), n = Inf)
cat("\nVIF:\n"); print(vif(model_bowl))
cat("\nBowling Role counts (check rare-category limitation):\n"); print(table(bowl_df$Role))

ggsave("fig17_bowling_regression_coefficients.png",
       ggplot(tidy(model_bowl, conf.int = TRUE) %>% filter(term != "(Intercept)"),
              aes(x = reorder(term, estimate), y = estimate)) +
         geom_point(size = 3, colour = "seagreen") +
         geom_errorbar(aes(ymin = conf.low, ymax = conf.high), width = 0.2) +
         geom_hline(yintercept = 0, linetype = "dashed", colour = "red") + coord_flip() +
         labs(title = "RQ5 (Bowling): Regression Coefficients for Log(Auction Price)",
              x = NULL, y = "Coefficient (log price scale)") + theme_minimal(),
       width = 7, height = 5)

png("fig18_bowling_residuals_vs_fitted.png", width = 600, height = 500); plot(model_bowl, which = 1); dev.off()
png("fig19_bowling_residuals_qqplot.png", width = 600, height = 500); plot(model_bowl, which = 2); dev.off()


# =============================================================================
# SECTION 8: RQ5 EXTENSION - OUT-OF-SAMPLE PREDICTION VALIDATION
# =============================================================================
# In-sample R-squared measures fit, not predictive accuracy. This section
# validates both models on held-out data via an 80/20 split and 5-fold CV.

cat("\n================ RQ5 Extension: Prediction Validation ================\n")

evaluate_split <- function(df, formula_str, label, test_prop = 0.2) {
  n <- nrow(df)
  test_idx <- sample(seq_len(n), size = floor(test_prop * n))
  train <- df[-test_idx, ]; test <- df[test_idx, ]
  model <- lm(as.formula(formula_str), data = train)
  pred <- tryCatch(predict(model, newdata = test), error = function(e) NULL)
  attempt <- 1
  while (is.null(pred) && attempt < 10) {
    test_idx <- sample(seq_len(n), size = floor(test_prop * n))
    train <- df[-test_idx, ]; test <- df[test_idx, ]
    model <- lm(as.formula(formula_str), data = train)
    pred <- tryCatch(predict(model, newdata = test), error = function(e) NULL)
    attempt <- attempt + 1
  }
  in_r2 <- summary(model)$r.squared
  out_r2 <- 1 - sum((test$log_price - pred)^2) / sum((test$log_price - mean(test$log_price))^2)
  rmse_val <- rmse(test$log_price, pred)
  cat(sprintf("%s: In-sample R2 = %.3f | Out-of-sample R2 = %.3f | RMSE = %.3f (%.2fx typical error)\n",
              label, in_r2, out_r2, rmse_val, exp(rmse_val)))
  list(out_r2 = out_r2, rmse = rmse_val, in_r2 = in_r2)
}

evaluate_kfold <- function(df, formula_str, label, k = 5) {
  set.seed(42)
  folds <- sample(rep(1:k, length.out = nrow(df)))
  r2s <- c(); rmses <- c(); skipped <- 0
  for (i in 1:k) {
    train <- df[folds != i, ]; test <- df[folds == i, ]
    result <- tryCatch({
      m <- lm(as.formula(formula_str), data = train)
      p <- predict(m, newdata = test)
      r2 <- 1 - sum((test$log_price - p)^2) / sum((test$log_price - mean(test$log_price))^2)
      list(r2 = r2, rmse = rmse(test$log_price, p))
    }, error = function(e) NULL)
    if (is.null(result)) skipped <- skipped + 1
    else { r2s <- c(r2s, result$r2); rmses <- c(rmses, result$rmse) }
  }
  cat(sprintf("%s 5-fold CV: %d/%d folds completed | mean R2 = %.3f (SD = %.3f) | mean RMSE = %.3f\n",
              label, length(r2s), k, mean(r2s), sd(r2s), mean(rmses)))
  list(mean_r2 = mean(r2s), sd_r2 = sd(r2s), skipped = skipped)
}

bat_formula  <- "log_price ~ strike_rate + runs + Role + Player_Origin"
bowl_formula <- "log_price ~ economy_rate + wickets + Role + Player_Origin"

cat("\n--- Table 12: Prediction validation summary ---\n")
bat_split  <- evaluate_split(bat_df, bat_formula, "BATTING")
bat_cv     <- evaluate_kfold(bat_df, bat_formula, "BATTING")
bowl_split <- evaluate_split(bowl_df, bowl_formula, "BOWLING")
bowl_cv    <- evaluate_kfold(bowl_df, bowl_formula, "BOWLING")

# Figure 20: predicted vs actual (batting, held-out test set)
n <- nrow(bat_df); test_idx <- sample(seq_len(n), size = floor(0.2 * n))
train <- bat_df[-test_idx, ]; test <- bat_df[test_idx, ]
m <- lm(as.formula(bat_formula), data = train); pred <- predict(m, newdata = test)
out_r2_plot <- 1 - sum((test$log_price - pred)^2) / sum((test$log_price - mean(test$log_price))^2)
ggsave("fig20_predicted_vs_actual.png",
       ggplot(data.frame(actual = test$log_price, predicted = pred), aes(x = actual, y = predicted)) +
         geom_point(alpha = 0.6, colour = "steelblue") +
         geom_abline(slope = 1, intercept = 0, linetype = "dashed", colour = "red") +
         labs(title = "Predicted vs Actual Log(Price) -- Batting Model, Test Set",
              subtitle = sprintf("Out-of-sample R-squared = %.3f. Points on the red line = perfect prediction.", out_r2_plot),
              x = "Actual log(price)", y = "Predicted log(price)") + theme_minimal(),
       width = 7, height = 5.5)


# =============================================================================
# SECTION 9: RQ6 - TOSS DECISION AND MATCH OUTCOME
# =============================================================================

cat("\n================ RQ6: Toss Decision and Match Outcome ================\n")

matches_valid <- matches %>%
  filter(!is.na(toss_winner), !is.na(winner), result != "no result") %>%
  mutate(toss_winner_won = toss_winner == winner)

cat("\n--- Table 13: contingency table ---\n")
ct <- table(matches_valid$toss_decision, matches_valid$toss_winner_won); print(ct)

chi <- chisq.test(ct)
cat(sprintf("\nChi-square = %.3f, df = %d, p = %.4g\n", chi$statistic, chi$parameter, chi$p.value))
cat("Expected cell counts:\n"); print(chi$expected)
cat(sprintf("Overall toss-winner win rate: %.1f%% (%d/%d)\n",
            mean(matches_valid$toss_winner_won) * 100,
            sum(matches_valid$toss_winner_won), nrow(matches_valid)))

rate_by_decision <- matches_valid %>% group_by(toss_decision) %>%
  summarise(win_rate = mean(toss_winner_won), n = n())
print(rate_by_decision)

ggsave("fig21_rq6_toss_decision.png",
       ggplot(rate_by_decision, aes(x = toss_decision, y = win_rate, fill = toss_decision)) +
         geom_col() + geom_hline(yintercept = 0.5, linetype = "dashed", colour = "grey40") +
         labs(title = "RQ6: Match Win Rate by Toss Decision",
              subtitle = sprintf("Chi-square, p = %.4g", chi$p.value),
              x = "Toss Decision", y = "Toss Winner's Match Win Rate") +
         theme_minimal() + theme(legend.position = "none"), width = 6, height = 5)


# =============================================================================
# SECTION 10: RQ6 EXTENSION - VENUE-STRATIFIED LOGISTIC REGRESSION
# =============================================================================
# Checks the toss effect is not driven by conditions at one or two grounds,
# restricted to venues with enough matches (>=30) for a meaningful comparison.

cat("\n================ RQ6 Extension: Venue-Stratified Analysis ================\n")

venue_counts <- matches_valid %>% count(venue, sort = TRUE)
top_venues <- venue_counts %>% filter(n >= 30) %>% pull(venue)

matches_top <- matches_valid %>%
  filter(venue %in% top_venues) %>%
  mutate(toss_decision = as.factor(toss_decision), venue = as.factor(venue),
         toss_winner_won_int = as.integer(toss_winner_won))

cat(sprintf("Analysing %d matches across %d venues with >=30 matches each\n",
            nrow(matches_top), length(top_venues)))

cat("\n--- Table 14: Venue-stratified logistic regression ---\n")
model_venue <- glm(toss_winner_won_int ~ toss_decision + venue, data = matches_top, family = binomial)
print(summary(model_venue))

coef_field <- coef(model_venue)["toss_decisionfield"]
or_field <- exp(coef_field)
ci <- exp(confint(model_venue)["toss_decisionfield", ])
cat(sprintf("\nOdds ratio (field vs bat): %.3f [95%% CI: %.3f, %.3f]\n", or_field, ci[1], ci[2]))

venue_summary <- matches_top %>% group_by(venue, toss_decision) %>%
  summarise(win_rate = mean(toss_winner_won_int), n = n(), .groups = "drop")

ggsave("fig22_rq6_venue_extension.png",
       ggplot(venue_summary, aes(x = reorder(venue, win_rate), y = win_rate, fill = toss_decision)) +
         geom_col(position = "dodge") + geom_hline(yintercept = 0.5, linetype = "dashed", colour = "grey40") +
         coord_flip() +
         labs(title = "RQ6 Extension: Toss-Winner Win Rate by Venue and Decision",
              subtitle = "Restricted to venues with >=30 matches",
              x = "Venue", y = "Toss Winner's Win Rate", fill = "Decision") + theme_minimal(),
       width = 8, height = 6)


# =============================================================================
# END OF SCRIPT
# =============================================================================
cat("\n================ Analysis complete. ================\n")
cat("All figures (fig1-fig22) and CSV outputs have been saved to the working directory.\n")
