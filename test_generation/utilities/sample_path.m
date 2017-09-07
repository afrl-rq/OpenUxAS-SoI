function [ pt_arr ] = sample_path( start_pt, end_pt )
%SAMPLE_PATH Summary of this function goes here
%   Detailed explanation goes here
num_dims = length(start_pt);
MINIMUM_ALTITUDE = 0;
MAXIMUM_ALTITUDE = 10;
NUM_OF_ALTITUDE_SAMPLES = 5;
MAXIMUM_ANGLE_CHANGE = pi/5;
ANGLE_SAMPLE_DEVIATION = pi;
MINIMUM_DISTANCE = 0.0001;
MAXIMUM_DISTANCE = 0.0015;
LAST_CONNECT_DISTANCE = 0.003;
pt_arr = start_pt;
angle_btw_pts = atan2(end_pt(1) - start_pt(1), end_pt(2) - start_pt(2));
last_pt = start_pt;
last_ang= angle_btw_pts;
last_ang_btw_pts = angle_btw_pts;
last_dist_btw_pts = sqrt((end_pt(2) - start_pt(2))^2 + (end_pt(1)-start_pt(1))^2);

while (abs(wrapToPi(last_ang_btw_pts - last_ang)) > MAXIMUM_ANGLE_CHANGE || last_dist_btw_pts > LAST_CONNECT_DISTANCE)
    len = MINIMUM_DISTANCE + rand(1) * (MAXIMUM_DISTANCE - MINIMUM_DISTANCE);
    ang = (ANGLE_SAMPLE_DEVIATION/2).*randn(1,1) + last_ang_btw_pts; % Mean of the distribution is towards the target
    ang = wrapToPi(ang);
    if wrapToPi(ang - last_ang) > MAXIMUM_ANGLE_CHANGE
        ang = wrapToPi(last_ang + MAXIMUM_ANGLE_CHANGE);
    elseif wrapToPi(ang - last_ang) < -MAXIMUM_ANGLE_CHANGE
        ang = wrapToPi(last_ang - MAXIMUM_ANGLE_CHANGE);
    end
    
    last_ang = wrapToPi(ang);
        
    if num_dims == 3
        last_pt = [last_pt(1) + len * sin(last_ang), last_pt(2) + len * cos(last_ang), last_pt(3)];
    else
        last_pt = [last_pt(1) + len * sin(last_ang), last_pt(2) + len * cos(last_ang)];
    end
    pt_arr(end+1, :) = last_pt;
    
    last_ang_btw_pts = atan2(end_pt(1) - last_pt(1), end_pt(2) - last_pt(2));
    last_dist_btw_pts = sqrt((end_pt(2) - last_pt(2))^2 + (end_pt(1)-last_pt(1))^2);
    if size(pt_arr, 1) > 2000
        break;
    end
    %disp(['last_pt: ', num2str(last_pt), ' last_ang: ', num2str(rad2deg(last_ang)), ' ang_btw_pts: ', num2str(rad2deg(last_ang_btw_pts)), ' dist: ', num2str(last_dist_btw_pts)]);
end
pt_arr(end+1, :) = end_pt;

if num_dims == 3
    altitude_x = linspace(1, size(pt_arr,1), NUM_OF_ALTITUDE_SAMPLES);
    altitude_y = (MAXIMUM_ALTITUDE - MINIMUM_ALTITUDE).*rand(1, NUM_OF_ALTITUDE_SAMPLES) + MINIMUM_ALTITUDE;
    altitude_y(1) = start_pt(3);
    altitude_y(end) = end_pt(3);
    altitude_xquery_pts = 1:size(pt_arr,1);
    altitude_profile = pchip(altitude_x, altitude_y, altitude_xquery_pts);
    for i = 1:size(pt_arr,1)
        pt_arr(i, 3) = altitude_profile(i);
    end
end

end

