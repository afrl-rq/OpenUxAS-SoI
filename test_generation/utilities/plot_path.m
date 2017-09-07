function [ f ] = plot_path( pt_arr )
%PLOT_PATH Summary of this function goes here
%   Detailed explanation goes here

f = figure;
plot3(pt_arr(end,2), pt_arr(end, 1), pt_arr(end, 3), 'x', 'color', 'r');
hold on;
plot3(pt_arr(1, 2), pt_arr(1, 1), pt_arr(1, 3), 'o', 'color', 'r');
hold on;
for i = 1:size(pt_arr, 1)
    plot3(pt_arr(i, 2), pt_arr(i, 1), pt_arr(i, 3), '.', 'color', 'b');
    hold on;
end
plot3(pt_arr(:,2), pt_arr(:,1), pt_arr(:,3), 'color', 'b');

end

