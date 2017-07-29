
PY_DIR='../../src/Utilities/heatmap/'
CURR_DIR=$(pwd)
HM_DIR='heatmapData'

cd $PY_DIR
# python3 add_keep_out_zones_from_heatmaps.py -cfg_path "$CURR_DIR/cfg_WaterwaySearch.xml" -heatmap_data_list "$CURR_DIR/$HM_DIR/dangerHeatmapData.csv" "$CURR_DIR/$HM_DIR/stealthHeatmapData.csv" -cl_level '0.95' '0.99995' -map_center '45.380' '-121' -map_width '11765' -map_height '9289'
python3 add_keep_out_zones_from_heatmaps.py -cfg_path "$CURR_DIR/cfg_WaterwaySearch.xml" -heatmap_data_list "$CURR_DIR/$HM_DIR/dangerHeatmapData.csv" "$CURR_DIR/$HM_DIR/failprobHeatmapData.csv" -cl_level '0.95' '0.95' -map_center '45.300' '-121' -map_width '11765' -map_height '9289'
cd $CURR_DIR

