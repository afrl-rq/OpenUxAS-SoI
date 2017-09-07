function [ pt_arr, P_arr ] = sample_path_and_keepout( start_pt, end_pt, P )
pt_arr = sample_path(start_pt, end_pt);
area_x_min = min(start_pt(2), end_pt(2));
area_x_max = max(start_pt(2), end_pt(2));
area_y_min = min(start_pt(1), end_pt(1));
area_y_max = max(start_pt(1), end_pt(1));
for i = 1:4
    new_P = placePolyhedron( P, area_x_min, area_x_max, area_y_min, area_y_max, pt_arr );
    P_arr(i) = new_P;
end

plot_path2d(pt_arr, 1);
hold on;
for i = 1:length(P_arr)
    P_arr(i).plot('wire', true, 'linewidth', 2);
end
end